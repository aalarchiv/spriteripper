// =========================================================
// Sprite Ripper - Main Application
//
// A tool for extracting sprite/font graphics from binary
// firmware and ROM files. Renders the entire binary as a
// scrollable pixel grid, with adjustable format settings.
//
// How it works:
//   1. The binary file is rendered as pixel rows, wrapped
//      into newspaper-style columns that fill the viewport
//      height. User scrolls horizontally.
//   2. The "start address" determines where line alignment
//      begins. Bytes before it are padded so the start
//      address lands at x=0 of a display row.
//   3. Frames (sprites) are highlighted with color tints.
//      Pixels inside frames get warm/cool/green/magenta
//      tints that alternate per frame.
//   4. User can select regions, adjust handles, and "Ack"
//      to apply the selection as start/width/height.
// =========================================================

'use strict';


// ---------------------------------------------------------
// DOM element references
// ---------------------------------------------------------

var $ = function(id) { return document.getElementById(id); };

var canvas    = $('canvas');
var ctx       = canvas.getContext('2d');
var preview   = $('preview');
var sizer     = $('sizer');
var dropzone  = $('dropzone');
var fileInput = $('fileInput');
var infoEl    = $('info');
var crossH    = $('crossH');
var crossV    = $('crossV');
var lensEl    = $('lens');
var lensCanvas = $('lensCanvas');
var lensCtx   = lensCanvas.getContext('2d');
var selRect   = $('selRect');


// ---------------------------------------------------------
// Application state
// ---------------------------------------------------------

var fileData = null;   // Uint8Array of loaded binary
var fileName = '';     // original filename for export

var renderPending = false;  // true while a render is queued
var postRender = null;      // callback to run after next render

var mouseInfo = '';    // address text shown in info box
var selInfo = '';      // selection text shown in info box

// Selection rectangle in canvas pixel coordinates.
// -1 means no selection.
var selX1 = -1, selY1 = -1, selX2 = -1, selY2 = -1;

// Pointer state
var lmbDown = false;      // left mouse button held
var rmbDown = false;      // right mouse button held
var dragMode = null;      // 'new' (new selection) or 'handle' (resizing)
var dragHandle = '';      // which handle: 'nw','n','ne','w','e','sw','s','se'
var handleFixed = {};     // snapshot of selection coords when handle drag started

// Mouse tracking for viewport anchor
var mouseInPreview = false;
var lastMouseVX = -1;     // mouse X relative to preview left edge
var lastMouseVY = -1;     // mouse Y relative to preview top edge

// Cached state from last render. Other modules read this
// to map between canvas coords and file byte addresses.
// Set inside render(), null before first render.
var RS = null;

// Previous zoom level, used to detect zoom changes.
// The slider updates its value before the event fires,
// so we track the old value ourselves.
var lastZoom = 2;


// ---------------------------------------------------------
// Constants
// ---------------------------------------------------------

// Magnifying lens: shows a 24x24 pixel area at 8x zoom
var LENS_R   = 12;              // source radius in canvas pixels
var LENS_MAG = 8;               // magnification factor
var LENS_PX  = LENS_R * 2 * LENS_MAG;  // lens display size (192px)

// Gap between wrapped columns in canvas pixels
var COL_GAP = 2;

lensCanvas.width  = LENS_PX;
lensCanvas.height = LENS_PX;


// ---------------------------------------------------------
// Utility functions
// ---------------------------------------------------------

// Parse a hex string like "1f3f8" or "0x1f3f8" to integer.
function parseHex(s) {
  return parseInt((s || '0').replace(/^0x/i, ''), 16) || 0;
}

// Format a byte value as 2-digit uppercase hex.
function hex8(v) {
  return (v & 0xFF).toString(16).toUpperCase().padStart(2, '0');
}

// Format a 16-bit value as 4-digit uppercase hex.
function hex16(v) {
  return (v & 0xFFFF).toString(16).toUpperCase().padStart(4, '0');
}


// ---------------------------------------------------------
// Parameters: read all UI controls into one object
// ---------------------------------------------------------

function getParams() {
  var bpp = Math.max(1, Math.min(8, parseInt($('inBpp').value) || 1));
  var enc = $('inEncoding').value;
  var ws  = parseInt($('inWordSize').value) || 16;
  var w   = Math.max(1, parseInt($('inWidth').value) || 1);
  var h   = Math.max(1, parseInt($('inHeight').value) || 1);

  var autoRow  = computeAutoRowBytes(w, bpp, enc, ws);
  var rowInput = parseInt($('inRowStride').value) || 0;
  var rs       = rowInput > 0 ? rowInput : autoRow;

  var fsInput = parseInt($('inFrameStride').value) || 0;
  var autoFS  = rs * h;
  // Frame stride semantics:
  //   > 0 : absolute byte count
  //   = 0 : auto (rowStride * height)
  //   < 0 : auto + value (negative = overlap)
  var frameStride = fsInput > 0 ? fsInput : autoFS + fsInput;

  return {
    bpp: bpp,
    encoding: enc,
    wordSize: ws,
    byteOrder: $('inByteOrder').value,
    msbFirst: $('inMsbFirst').checked,
    width: w,
    height: h,
    count: Math.max(1, parseInt($('inCount').value) || 1),
    rowStride: rs,
    frameStride: frameStride,
    startAddr: parseHex($('inStartAddr').value),
    zoom: parseInt($('inZoom').value) || 2
  };
}

// Compute the number of bytes one pixel row occupies,
// based on the encoding format. This is the "natural"
// row stride with no extra padding.
function computeAutoRowBytes(w, bpp, enc, ws) {
  if (enc === 'chunky') {
    // Packed pixels: width * bpp bits, rounded up to bytes
    return Math.ceil(w * bpp / 8);
  }
  if (enc === 'planar_line') {
    // Each row has bpp plane-sub-rows, each ceil(w/8) bytes
    return Math.ceil(w / 8) * bpp;
  }
  // planar_word: groups of bpp words, each covering wordSize*8 pixels
  var wBits = ws * 8;
  return Math.ceil(w / wBits) * ws * bpp;
}


// ---------------------------------------------------------
// Pixel reader
//
// Reads the color value (0..2^bpp-1) of one pixel at
// column x in a row that starts at file byte rowStart.
// Returns -1 if the pixel is outside the file (padding).
// ---------------------------------------------------------

// Safe byte read: returns 0 for out-of-bounds addresses.
function getByte(bi) {
  return (bi >= 0 && bi < fileData.length) ? fileData[bi] : 0;
}

// Check if a byte index is inside the file.
function inBounds(bi) {
  return bi >= 0 && bi < fileData.length;
}

function readPx(rowStart, x, p) {
  var bpp = p.bpp;
  var encoding = p.encoding;
  var ws = p.wordSize;
  var bo = p.byteOrder;
  var msb = p.msbFirst;

  // --- Chunky (packed pixels) ---
  // Each pixel is bpp consecutive bits in the byte stream.
  if (encoding === 'chunky') {
    var firstBi = rowStart + Math.floor(x * bpp / 8);
    if (!inBounds(firstBi)) return -1;

    var val = 0;
    for (var i = 0; i < bpp; i++) {
      var sbit = x * bpp + i;
      var bi = rowStart + Math.floor(sbit / 8);
      var bitInByte = msb ? (7 - (sbit % 8)) : (sbit % 8);
      if (msb) {
        val = (val << 1) | ((getByte(bi) >> bitInByte) & 1);
      } else {
        val |= ((getByte(bi) >> bitInByte) & 1) << i;
      }
    }
    return val;
  }

  // --- Planar formats ---
  // The pixel value is assembled from one bit per bitplane.
  var anyInBounds = false;
  var val = 0;

  if (encoding === 'planar_line') {
    // Line-interleaved: each row stores plane0 bytes, then plane1, etc.
    // Used by Game Boy (2bpp), some NES formats.
    var prb = Math.ceil(p.width / 8);  // bytes per plane per row
    var bitPos = msb ? (7 - (x % 8)) : (x % 8);
    for (var pl = 0; pl < bpp; pl++) {
      var bi = rowStart + pl * prb + Math.floor(x / 8);
      if (inBounds(bi)) {
        anyInBounds = true;
        val |= ((fileData[bi] >> bitPos) & 1) << pl;
      }
    }
  } else {
    // Word-interleaved: planes interleaved per word group.
    // Each group has bpp words covering wordSize*8 pixels.
    // Used by Atari ST (4bpp/16bit), SNES.
    var wBits = ws * 8;
    var wBytes = ws;
    var grp = Math.floor(x / wBits);      // which word group
    var pix = x % wBits;                   // pixel within group
    var bpw = msb ? (wBits - 1 - pix) : pix;  // bit position in word
    // Byte within the word depends on endianness
    var biw = (bo === 'big')
      ? (wBytes - 1 - Math.floor(bpw / 8))
      : Math.floor(bpw / 8);
    var bib = bpw % 8;                    // bit within that byte
    var grpBytes = wBytes * bpp;           // bytes per group
    for (var pl = 0; pl < bpp; pl++) {
      var bi = rowStart + grp * grpBytes + pl * wBytes + biw;
      if (inBounds(bi)) {
        anyInBounds = true;
        val |= ((fileData[bi] >> bib) & 1) << pl;
      }
    }
  }

  return anyInBounds ? val : -1;
}

// Return the file byte address for pixel x in a row.
// Used for mouse-over address display and selection info.
function pixelFileByte(rowStart, x, p) {
  if (p.encoding === 'chunky') {
    return rowStart + Math.floor(x * p.bpp / 8);
  }
  if (p.encoding === 'planar_line') {
    return rowStart + Math.floor(x / 8);
  }
  // planar_word
  var wBits = p.wordSize * 8;
  return rowStart + Math.floor(x / wBits) * p.wordSize * p.bpp;
}


// ---------------------------------------------------------
// Coordinate mapping
//
// The display canvas is divided into side-by-side columns,
// each p.width pixels wide with COL_GAP px gaps between.
// Each column shows colHeight consecutive display lines.
//
// "padBytes" blank bytes are prepended so the startAddr
// byte lands at x=0 of a display row.
// ---------------------------------------------------------

// Convert canvas pixel (cx, cy) to a file byte address.
// Returns -1 if the pixel is in a gap, padding, or outside.
function canvasToFileByte(cx, cy) {
  if (!RS) return -1;
  var cW = RS.p.width + COL_GAP;
  var wc = Math.floor(cx / cW);        // which column
  var lx = cx - wc * cW;               // x within column
  if (wc >= RS.wrapCols || lx < 0 || lx >= RS.p.width) return -1;

  var gl = wc * RS.colHeight + cy;     // global display line
  if (gl < 0 || gl >= RS.totalLines) return -1;

  var rowStart = gl * RS.p.rowStride - RS.padBytes;
  var fb = pixelFileByte(rowStart, lx, RS.p);
  return inBounds(fb) ? fb : -1;
}

// Convert a file byte address to canvas pixel position.
// Returns null if the byte is outside the visible area.
function fileByteToCanvas(fb) {
  if (!RS) return null;
  var gb = fb + RS.padBytes;
  if (gb < 0) return null;

  var gl  = Math.floor(gb / RS.p.rowStride);
  var rem = gb % RS.p.rowStride;
  var wc  = Math.floor(gl / RS.colHeight);
  var row = gl % RS.colHeight;

  // Approximate pixel-x from the byte remainder
  var gx = 0;
  if (RS.p.encoding === 'chunky' && RS.p.bpp > 0) {
    gx = Math.floor(rem * 8 / RS.p.bpp);
  } else if (RS.p.encoding === 'planar_line') {
    gx = rem * 8;
  } else {
    var wBits = RS.p.wordSize * 8;
    var grpB = RS.p.wordSize * RS.p.bpp;
    if (grpB > 0) gx = Math.floor(rem / grpB) * wBits;
  }

  if (wc >= RS.wrapCols) return null;
  return {
    x: wc * (RS.p.width + COL_GAP) + Math.min(gx, RS.p.width - 1),
    y: row
  };
}


// ---------------------------------------------------------
// Renderer
//
// Draws the entire binary file onto the canvas as a grid
// of pixel columns. Each column is viewport-height tall
// (so the user scrolls horizontally to scan the file).
//
// Pixels inside sprite frames are tinted with alternating
// colors so frame boundaries are visible per-pixel.
// ---------------------------------------------------------

function render(preserveSel) {
  if (!fileData) return;

  // Optionally preserve the selection across re-render
  var savedSel = preserveSel ? selToAddr() : null;
  if (!preserveSel) clearSel();

  var p  = getParams();
  var rs = p.rowStride;

  // -- Padding --
  // Insert blank bytes so startAddr lands at x=0 of a row.
  var padBytes = (rs - (p.startAddr % rs)) % rs;
  var totalDataBytes = padBytes + fileData.length;
  var totalLines = Math.ceil(totalDataBytes / rs);

  // -- Column layout --
  // Each column is as tall as the viewport. Scroll is horizontal.
  var colHeight = Math.max(1, Math.floor(preview.clientHeight / p.zoom) - 1);
  var maxCols   = Math.max(1, Math.floor(65536 / (p.width + COL_GAP)));
  var wrapCols  = Math.min(maxCols, Math.max(1, Math.ceil(totalLines / colHeight)));
  var cW = wrapCols * p.width + Math.max(0, wrapCols - 1) * COL_GAP;
  var cH = colHeight;
  if (cW < 1 || cH < 1) return;

  canvas.width  = cW;
  canvas.height = cH;

  // Cache render state for coordinate mapping and anchoring
  RS = {
    p: p,
    totalLines: totalLines,
    wrapCols: wrapCols,
    colHeight: colHeight,
    padBytes: padBytes
  };

  // -- Grayscale palette --
  var maxVal = (1 << p.bpp) - 1 || 1;
  var palette = new Uint8Array(maxVal + 1);
  for (var i = 0; i <= maxVal; i++) {
    palette[i] = Math.round(i / maxVal * 255);
  }

  // -- Frame tinting --
  // Returns which frame (0..count-1) a file byte belongs to,
  // or -1 if it is in a gap or outside any frame.
  var frameDataSize = rs * p.height;
  function frameForByte(fb) {
    var off = fb - p.startAddr;
    if (off < 0) return -1;
    var fi = Math.floor(off / p.frameStride);
    if (fi >= p.count || fi < 0) return -1;
    return (off - fi * p.frameStride) < frameDataSize ? fi : -1;
  }

  // Tint multipliers: [r, g, b, base_add]
  // base_add gives a faint glow even on black pixels
  var tints = [
    [1,   0.75, 0.45, 12],   // warm amber
    [0.45, 0.8,  1,   12],   // cool cyan
    [0.55, 1,    0.55, 12],  // green
    [1,    0.55, 0.85, 12]   // magenta
  ];

  // -- Render loop: column by column, in vertical strips --
  var STRIP = 512;
  for (var wc = 0; wc < wrapCols; wc++) {
    var colStartLine = wc * colHeight;
    var xOffset = wc * (p.width + COL_GAP);

    for (var sy = 0; sy < cH; sy += STRIP) {
      var sh = Math.min(STRIP, cH - sy);
      var img = new ImageData(p.width, sh);
      var px = img.data;

      for (var y = 0; y < sh; y++) {
        var gl = colStartLine + sy + y;
        if (gl >= totalLines) break;
        var rowStart = gl * rs - padBytes;

        // Optimization: check if this whole row is in one frame.
        // If yes, we skip per-pixel frameForByte lookups.
        var fi0 = frameForByte(pixelFileByte(rowStart, 0, p));
        var fi1 = frameForByte(pixelFileByte(rowStart, p.width - 1, p));

        if (fi0 === fi1) {
          // Fast path: entire row has the same tint
          var t = fi0 >= 0 ? tints[fi0 % tints.length] : null;
          for (var x = 0; x < p.width; x++) {
            var v = readPx(rowStart, x, p);
            var idx = (y * p.width + x) << 2;
            if (v >= 0) {
              var c = palette[v];
              if (t) {
                px[idx]     = Math.min(255, (c * t[0] | 0) + t[3]);
                px[idx + 1] = Math.min(255, (c * t[1] | 0) + t[3]);
                px[idx + 2] = Math.min(255, (c * t[2] | 0) + t[3]);
              } else {
                px[idx] = c; px[idx + 1] = c; px[idx + 2] = c;
              }
              px[idx + 3] = 255;
            }
          }
        } else {
          // Slow path: frame boundary crosses this row,
          // so we check each pixel individually.
          for (var x = 0; x < p.width; x++) {
            var v = readPx(rowStart, x, p);
            var idx = (y * p.width + x) << 2;
            if (v >= 0) {
              var c = palette[v];
              var fi = frameForByte(pixelFileByte(rowStart, x, p));
              if (fi >= 0) {
                var t = tints[fi % tints.length];
                px[idx]     = Math.min(255, (c * t[0] | 0) + t[3]);
                px[idx + 1] = Math.min(255, (c * t[1] | 0) + t[3]);
                px[idx + 2] = Math.min(255, (c * t[2] | 0) + t[3]);
              } else {
                px[idx] = c; px[idx + 1] = c; px[idx + 2] = c;
              }
              px[idx + 3] = 255;
            }
          }
        }
      }

      ctx.putImageData(img, xOffset, sy);
    }
  }

  updateDisplay();
  if (savedSel) addrToSel(savedSel);
  refreshInfo();
}

// Update CSS sizing so scrollbars match the zoomed canvas.
function updateDisplay() {
  var z = parseInt($('inZoom').value) || 2;
  sizer.style.width  = (canvas.width  * z) + 'px';
  sizer.style.height = (canvas.height * z) + 'px';
  canvas.style.transform = 'scale(' + z + ')';
  $('zoomVal').textContent = z + '\u00d7';
  updateSelCSS();
}


// ---------------------------------------------------------
// Selection
//
// The user drags on the canvas to create a selection box.
// Handles on edges/corners allow resizing. The "Ack" button
// applies the selection as new start address, width, height.
// ---------------------------------------------------------

function clearSel() {
  selX1 = selY1 = selX2 = selY2 = -1;
  selRect.style.display = 'none';
  selInfo = '';
}

function hasSel() {
  return selX1 >= 0;
}

// Convert selection from canvas coords to file byte addresses.
// Used to preserve the selection across re-renders.
function selToAddr() {
  if (!hasSel() || !RS) return null;
  var r1 = canvasToFileByte(Math.min(selX1, selX2), Math.min(selY1, selY2));
  var r2 = canvasToFileByte(Math.max(selX1, selX2), Math.max(selY1, selY2));
  if (r1 < 0 || r2 < 0) return null;
  return {
    b1: r1,
    b2: r2,
    w: Math.abs(selX2 - selX1) + 1,
    h: Math.abs(selY2 - selY1) + 1
  };
}

// Restore selection from file byte addresses after re-render.
function addrToSel(sa) {
  if (!sa || !RS) { clearSel(); return; }
  var p1 = fileByteToCanvas(sa.b1);
  var p2 = fileByteToCanvas(sa.b2);
  if (!p1 || !p2) { clearSel(); return; }
  selX1 = p1.x;
  selY1 = p1.y;
  selX2 = p1.x + sa.w - 1;
  selY2 = p1.y + sa.h - 1;
  updateSelCSS();
  computeSelInfo();
}

// Update the selection rectangle DOM element position and size.
// Border width and handle size scale with zoom for visibility.
function updateSelCSS() {
  if (!hasSel()) { selRect.style.display = 'none'; return; }
  var z  = parseInt($('inZoom').value) || 2;
  var sx = Math.min(selX1, selX2);
  var sy = Math.min(selY1, selY2);
  var w  = Math.abs(selX2 - selX1) + 1;
  var h  = Math.abs(selY2 - selY1) + 1;
  var bw = Math.max(2, Math.ceil(z / 2));
  var hs = Math.max(6, bw * 3);

  selRect.style.display     = 'block';
  selRect.style.left        = (sx * z) + 'px';
  selRect.style.top         = (sy * z) + 'px';
  selRect.style.width       = (w * z) + 'px';
  selRect.style.height      = (h * z) + 'px';
  selRect.style.borderWidth = bw + 'px';

  selRect.querySelectorAll('.sel-handle').forEach(function(el) {
    el.style.width  = hs + 'px';
    el.style.height = hs + 'px';
  });
}

// Update the selection info text shown in the info box.
function computeSelInfo() {
  if (!hasSel() || !RS) { selInfo = ''; return; }
  var sx = Math.min(selX1, selX2);
  var sy = Math.min(selY1, selY2);
  var w  = Math.abs(selX2 - selX1) + 1;
  var h  = Math.abs(selY2 - selY1) + 1;
  var b1 = canvasToFileByte(sx, sy);
  if (b1 < 0) { selInfo = ''; return; }
  var bEnd = b1 + RS.p.rowStride * h;
  selInfo = 'S:0x' + b1.toString(16).toUpperCase()
    + ' E:0x' + bEnd.toString(16).toUpperCase()
    + ' ' + w + '\u00d7' + h
    + ' ' + (bEnd - b1) + 'B';
}


// ---------------------------------------------------------
// Selection handle resize
//
// When the user clicks near an edge or corner of the
// selection, they can drag to resize it. Hit testing is
// done programmatically (the handle elements are visual only).
// ---------------------------------------------------------

// Check if canvas coords (cx, cy) are near a selection edge.
// Returns a handle name or null.
function hitTestSel(cx, cy) {
  if (!hasSel()) return null;
  var z = parseInt($('inZoom').value) || 2;
  var m = Math.max(2, Math.round(8 / z));  // hit margin in canvas px

  var sx = selX1, sy = selY1, ex = selX2, ey = selY2;
  var nL = Math.abs(cx - sx) <= m;
  var nR = Math.abs(cx - ex) <= m;
  var nT = Math.abs(cy - sy) <= m;
  var nB = Math.abs(cy - ey) <= m;
  var inX = cx >= sx - m && cx <= ex + m;
  var inY = cy >= sy - m && cy <= ey + m;

  // Corners first (higher priority)
  if (nT && nL) return 'nw';
  if (nT && nR) return 'ne';
  if (nB && nL) return 'sw';
  if (nB && nR) return 'se';
  // Then edges
  if (nT && inX) return 'n';
  if (nB && inX) return 's';
  if (nL && inY) return 'w';
  if (nR && inY) return 'e';
  return null;
}

// Begin a handle drag. Snapshot the current selection so
// the opposite edge stays fixed while the dragged edge moves.
function startDrag(h) {
  dragMode = 'handle';
  dragHandle = h;
  handleFixed = { x1: selX1, y1: selY1, x2: selX2, y2: selY2 };
}

// Move the dragged edge/corner to (cx, cy). The opposite
// edge stays at the snapshotted position.
function applyDrag(cx, cy) {
  var h = dragHandle;
  var f = handleFixed;
  if      (h === 'nw') { selX1 = cx; selY1 = cy; selX2 = f.x2; selY2 = f.y2; }
  else if (h === 'ne') { selX2 = cx; selY1 = cy; selX1 = f.x1; selY2 = f.y2; }
  else if (h === 'sw') { selX1 = cx; selY2 = cy; selX2 = f.x2; selY1 = f.y1; }
  else if (h === 'se') { selX2 = cx; selY2 = cy; selX1 = f.x1; selY1 = f.y1; }
  else if (h === 'n')  { selY1 = cy; selX1 = f.x1; selX2 = f.x2; selY2 = f.y2; }
  else if (h === 's')  { selY2 = cy; selX1 = f.x1; selX2 = f.x2; selY1 = f.y1; }
  else if (h === 'w')  { selX1 = cx; selY1 = f.y1; selX2 = f.x2; selY2 = f.y2; }
  else if (h === 'e')  { selX2 = cx; selY1 = f.y1; selX1 = f.x1; selY2 = f.y2; }
}


// ---------------------------------------------------------
// Ack button: apply selection to start/width/height
// ---------------------------------------------------------

$('btnAck').addEventListener('click', function() {
  if (!hasSel() || !RS) return;
  var sx = Math.min(selX1, selX2);
  var sy = Math.min(selY1, selY2);
  var w  = Math.abs(selX2 - selX1) + 1;
  var h  = Math.abs(selY2 - selY1) + 1;
  var fb = canvasToFileByte(sx, sy);
  if (fb < 0) return;

  $('inStartAddr').value = fb.toString(16);
  $('inWidth').value = w;
  $('inHeight').value = h;
  clearSel();
  scheduleRenderAndFocus();
});


// ---------------------------------------------------------
// Info box: shows mouse address and selection details
// ---------------------------------------------------------

function refreshInfo() {
  var h = '';
  if (mouseInfo) h += '<span class="ptr">' + mouseInfo + '</span>\n';
  if (selInfo)   h += '<span class="sel">' + selInfo + '</span>\n';
  infoEl.innerHTML = h || '\u2014';
}


// ---------------------------------------------------------
// Magnifying lens
//
// Shows an 8x magnified view of the area around the cursor.
// Displayed when holding LMB (drag) or RMB (inspect).
// ---------------------------------------------------------

function showLens(e, cx, cy) {
  lensEl.style.display = 'block';

  // Position near cursor, flip if it would go offscreen
  var lx = e.clientX + 24;
  var ly = e.clientY - LENS_PX - 28;
  if (lx + LENS_PX + 4 > window.innerWidth) lx = e.clientX - LENS_PX - 28;
  if (ly < 0) ly = e.clientY + 24;
  lensEl.style.left = lx + 'px';
  lensEl.style.top  = ly + 'px';

  // Draw magnified region from the main canvas
  lensCtx.imageSmoothingEnabled = false;
  lensCtx.fillStyle = '#15171e';
  lensCtx.fillRect(0, 0, LENS_PX, LENS_PX);
  lensCtx.drawImage(canvas,
    cx - LENS_R, cy - LENS_R, LENS_R * 2, LENS_R * 2,
    0, 0, LENS_PX, LENS_PX);

  // Draw pixel grid lines
  lensCtx.strokeStyle = 'rgba(255,255,255,.06)';
  lensCtx.lineWidth = 1;
  lensCtx.beginPath();
  for (var i = 1; i < LENS_R * 2; i++) {
    var q = i * LENS_MAG + 0.5;
    lensCtx.moveTo(q, 0); lensCtx.lineTo(q, LENS_PX);
    lensCtx.moveTo(0, q); lensCtx.lineTo(LENS_PX, q);
  }
  lensCtx.stroke();

  // Draw center crosshair
  lensCtx.strokeStyle = 'rgba(0,255,68,.5)';
  lensCtx.beginPath();
  lensCtx.moveTo(LENS_PX / 2 + 0.5, 0);
  lensCtx.lineTo(LENS_PX / 2 + 0.5, LENS_PX);
  lensCtx.moveTo(0, LENS_PX / 2 + 0.5);
  lensCtx.lineTo(LENS_PX, LENS_PX / 2 + 0.5);
  lensCtx.stroke();
}

function hideLens() {
  lensEl.style.display = 'none';
}

// Convert a pointer event to canvas pixel coordinates.
function canvasCoord(e) {
  var r = canvas.getBoundingClientRect();
  var z = parseInt($('inZoom').value) || 2;
  return {
    x: Math.floor((e.clientX - r.left) / z),
    y: Math.floor((e.clientY - r.top)  / z)
  };
}


// ---------------------------------------------------------
// Viewport anchor
//
// Before re-rendering, we capture a "anchor" -- a file byte
// address and its current viewport position. After render,
// we scroll so that byte appears at the same screen spot.
// This keeps the view stable when changing parameters.
// ---------------------------------------------------------

function computeAnchor() {
  if (!RS) return null;
  var z = RS.p.zoom;

  // Priority 1: byte under the mouse pointer
  if (mouseInPreview && lastMouseVX >= 0) {
    var cx = Math.floor((lastMouseVX + preview.scrollLeft) / z);
    var cy = Math.floor((lastMouseVY + preview.scrollTop) / z);
    var fb = canvasToFileByte(cx, cy);
    if (fb >= 0) return { byte: fb, vpx: lastMouseVX, vpy: lastMouseVY };
  }

  // Priority 2: sprite start address (if currently visible)
  var pos = fileByteToCanvas(RS.p.startAddr);
  if (pos) {
    var vx = pos.x * z - preview.scrollLeft;
    var vy = pos.y * z - preview.scrollTop;
    if (vx > -RS.p.width * z && vx < preview.clientWidth &&
        vy > -RS.p.height * z && vy < preview.clientHeight) {
      return { byte: RS.p.startAddr, vpx: vx, vpy: vy };
    }
  }

  // Priority 3: byte at the center of the viewport
  var cx = Math.floor((preview.clientWidth / 2 + preview.scrollLeft) / z);
  var cy = Math.floor((preview.clientHeight / 2 + preview.scrollTop) / z);
  var fb = canvasToFileByte(cx, cy);
  if (fb >= 0) return { byte: fb, vpx: preview.clientWidth / 2, vpy: preview.clientHeight / 2 };

  return null;
}

// After re-render, scroll so the anchor byte is at its
// original viewport position.
function applyAnchor(a) {
  if (!a || !RS) return;
  var z = RS.p.zoom;
  var pos = fileByteToCanvas(a.byte);
  if (!pos) return;
  preview.scrollLeft = pos.x * z - a.vpx;
  preview.scrollTop  = pos.y * z - a.vpy;
}

// Zoom to a specific level, preserving viewport anchor
// and selection.
function doZoom(nz) {
  nz = Math.max(1, Math.min(16, nz));
  var oz = lastZoom;
  if (nz === oz) return;

  var anchor = computeAnchor();
  var ss = selToAddr();
  lastZoom = nz;
  $('inZoom').value = nz;

  // Render synchronously so we can restore anchor immediately
  renderPending = false;
  render(true);
  if (ss) addrToSel(ss);
  if (anchor) applyAnchor(anchor);
}


// ---------------------------------------------------------
// Pointer events: crosshair, lens, selection, magnifier
// ---------------------------------------------------------

// Suppress browser context menu on the preview area
preview.addEventListener('contextmenu', function(e) {
  e.preventDefault();
});

// Pointer down: start selection (LMB) or magnifier (RMB)
preview.addEventListener('pointerdown', function(e) {
  if (!fileData) return;

  // Right mouse button: magnifier only, no selection
  if (e.button === 2) {
    e.preventDefault();
    rmbDown = true;
    preview.setPointerCapture(e.pointerId);
    var c = canvasCoord(e);
    showLens(e, c.x, c.y);
    return;
  }

  if (e.button !== 0) return;
  e.preventDefault();
  preview.setPointerCapture(e.pointerId);
  lmbDown = true;

  var c = canvasCoord(e);

  // Check if clicking near an existing selection edge
  var h = hitTestSel(c.x, c.y);
  if (h) {
    startDrag(h);
    showLens(e, c.x, c.y);
    return;
  }

  // Otherwise start a new selection
  dragMode = 'new';
  selX1 = c.x; selY1 = c.y;
  selX2 = c.x; selY2 = c.y;
  updateSelCSS();
  showLens(e, c.x, c.y);
});

// Pointer move: update crosshair, address, lens, selection
preview.addEventListener('pointermove', function(e) {
  if (!fileData) return;
  var c = canvasCoord(e);

  // Track mouse position for viewport anchor
  var pr = preview.getBoundingClientRect();
  lastMouseVX = e.clientX - pr.left;
  lastMouseVY = e.clientY - pr.top;

  // Position the crosshair lines
  crossH.style.display = 'block';
  crossV.style.display = 'block';
  crossH.style.top    = e.clientY + 'px';
  crossH.style.left   = pr.left + 'px';
  crossH.style.width  = pr.width + 'px';
  crossV.style.left   = e.clientX + 'px';
  crossV.style.top    = pr.top + 'px';
  crossV.style.height = pr.height + 'px';

  // Show address of pixel under cursor
  var fb = canvasToFileByte(c.x, c.y);
  mouseInfo = fb >= 0 ? '0x' + fb.toString(16).toUpperCase() : '';

  // Update selection or lens during drag
  if (lmbDown) {
    if (dragMode === 'new') {
      selX2 = c.x;
      selY2 = c.y;
    } else if (dragMode === 'handle') {
      applyDrag(c.x, c.y);
    }
    updateSelCSS();
    computeSelInfo();
    showLens(e, c.x, c.y);
  }

  // RMB magnifier (no selection)
  if (rmbDown) {
    showLens(e, c.x, c.y);
  }

  refreshInfo();
});

// Pointer up: finalize selection or hide magnifier
preview.addEventListener('pointerup', function(e) {
  if (e.button === 2 && rmbDown) {
    rmbDown = false;
    hideLens();
    return;
  }
  if (e.button !== 0 || !lmbDown) return;
  lmbDown = false;
  hideLens();
  dragMode = null;

  // Normalize selection so x1/y1 is always top-left
  var sx = Math.min(selX1, selX2);
  var sy = Math.min(selY1, selY2);
  selX1 = sx;
  selY1 = sy;
  selX2 = Math.max(selX1, selX2);
  selY2 = Math.max(selY1, selY2);
  computeSelInfo();
  refreshInfo();
});

preview.addEventListener('pointerenter', function() {
  mouseInPreview = true;
});

preview.addEventListener('pointerleave', function() {
  mouseInPreview = false;
  if (lmbDown || rmbDown) return;
  crossH.style.display = 'none';
  crossV.style.display = 'none';
  mouseInfo = '';
  lastMouseVX = -1;
  refreshInfo();
});


// ---------------------------------------------------------
// Focus: scroll to show the start address
// ---------------------------------------------------------

function scrollToStart() {
  if (!RS) return;
  var pos = fileByteToCanvas(RS.p.startAddr);
  if (!pos) return;
  var z = RS.p.zoom;
  preview.scrollTo({
    left: Math.max(0, pos.x * z - preview.clientWidth / 3),
    top: Math.max(0, pos.y * z - 20),
    behavior: 'smooth'
  });
}

$('btnFocus').addEventListener('click', function() {
  if (fileData && RS) scrollToStart();
});


// ---------------------------------------------------------
// Export: save sprites as PNG or Intel HEX
// ---------------------------------------------------------

$('saveFormat').addEventListener('change', function() {
  $('btnSave').textContent = 'Save ' + $('saveFormat').value.toUpperCase();
});

// Clean up a filename for use in exports.
function sanitize(s) {
  return s.replace(/\.[^.]+$/, '')
    .replace(/[^a-zA-Z0-9_\-]/g, '_')
    .replace(/_+/g, '_')
    .replace(/^_|_$/g, '') || 'bin';
}

// CRC16 hash for short file identifier in export names.
function crc16(d) {
  var c = 0xFFFF;
  for (var i = 0; i < d.length; i++) {
    c ^= d[i];
    for (var j = 0; j < 8; j++) {
      c = c & 1 ? (c >>> 1) ^ 0xA001 : c >>> 1;
    }
  }
  return c & 0xFFFF;
}

// Trigger a file download from a Blob.
function dlBlob(blob, name) {
  var a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(a.href);
}

// Build export filename:
// {binname}_{crc}_{spritename}_{bytesize}_{hexaddr}.{ext}
function expName(si, ext) {
  var p = getParams();
  var base = sanitize(fileName);
  var hash = hex16(crc16(fileData));
  var sn = ($('inSpriteName').value.trim() || 'sprite').replace(/[^a-zA-Z0-9_\-]/g, '_');
  var addr = p.startAddr + si * p.frameStride;
  var bytes = p.rowStride * p.height;
  return base + '_' + hash + '_' + sn + '_' + bytes + '_' + addr.toString(16).toUpperCase() + '.' + ext;
}

// Encode raw bytes as Intel HEX format string.
function toIHex(data, base) {
  var out = '';
  var curUpper = -1;
  var BYTES_PER_LINE = 16;

  for (var off = 0; off < data.length; off += BYTES_PER_LINE) {
    var addr = base + off;
    var upper = (addr >>> 16) & 0xFFFF;

    // Emit extended linear address record when upper 16 bits change
    if (upper !== curUpper) {
      curUpper = upper;
      var s = 2 + 4 + (upper >> 8) + (upper & 0xFF);
      out += ':02000004' + hex16(upper) + hex8((256 - (s & 0xFF)) & 0xFF) + '\n';
    }

    var len = Math.min(BYTES_PER_LINE, data.length - off);
    var lo = addr & 0xFFFF;
    var s = len + (lo >> 8) + (lo & 0xFF);
    var line = ':' + hex8(len) + hex16(lo) + '00';
    for (var i = 0; i < len; i++) {
      line += hex8(data[off + i]);
      s += data[off + i];
    }
    out += line + hex8((256 - (s & 0xFF)) & 0xFF) + '\n';
  }

  return out + ':00000001FF\n';
}

// Save button handler: export all frames + JSON metadata
$('btnSave').addEventListener('click', async function() {
  if (!fileData) return;
  var p = getParams();
  var fmt = $('saveFormat').value;
  var allMeta = [];
  var maxVal = (1 << p.bpp) - 1 || 1;
  var pal = new Uint8Array(maxVal + 1);
  for (var i = 0; i <= maxVal; i++) pal[i] = Math.round(i / maxVal * 255);

  for (var si = 0; si < p.count; si++) {
    var frameStart = p.startAddr + si * p.frameStride;

    // Metadata for this frame
    allMeta.push({
      parentFile: fileName,
      name: ($('inSpriteName').value || 'sprite') + '_' + String(si).padStart(3, '0'),
      address: '0x' + frameStart.toString(16),
      width: p.width, height: p.height,
      bpp: p.bpp, encoding: p.encoding,
      wordSize: p.wordSize, byteOrder: p.byteOrder, msbFirst: p.msbFirst,
      rowStride: p.rowStride, frameStride: p.frameStride
    });

    if (fmt === 'png') {
      // Render the frame to an offscreen canvas and export as PNG
      var tc = document.createElement('canvas');
      tc.width = p.width;
      tc.height = p.height;
      var tctx = tc.getContext('2d');
      var img = new ImageData(p.width, p.height);
      var px = img.data;
      for (var y = 0; y < p.height; y++) {
        var rs = frameStart + y * p.rowStride;
        for (var x = 0; x < p.width; x++) {
          var v = readPx(rs, x, p);
          var idx = (y * p.width + x) << 2;
          if (v >= 0) {
            var c = pal[v];
            px[idx] = c; px[idx + 1] = c; px[idx + 2] = c; px[idx + 3] = 255;
          }
        }
      }
      tctx.putImageData(img, 0, 0);
      var blob = await new Promise(function(r) { tc.toBlob(r, 'image/png'); });
      dlBlob(blob, expName(si, 'png'));
    } else {
      // Export raw bytes as Intel HEX
      var sB = frameStart;
      var eB = frameStart + p.rowStride * p.height;
      var raw = fileData.slice(Math.max(0, sB), Math.min(eB, fileData.length));
      dlBlob(new Blob([toIHex(raw, sB)], { type: 'text/plain' }), expName(si, 'hex'));
    }

    // Small delay between downloads to avoid browser blocking
    if (p.count > 1) await new Promise(function(r) { setTimeout(r, 120); });
  }

  // Save JSON metadata for the whole export
  var metaName = sanitize(fileName) + '_' + hex16(crc16(fileData)) + '_'
    + (($('inSpriteName').value.trim() || 'sprite').replace(/[^a-zA-Z0-9_\-]/g, '_'))
    + '_0_' + p.startAddr.toString(16).toUpperCase() + '.json';
  var metaObj = {
    exportDate: new Date().toISOString(),
    parentFile: fileName,
    format: fmt,
    sprites: allMeta
  };
  dlBlob(new Blob([JSON.stringify(metaObj, null, 2)], { type: 'application/json' }), metaName);
});


// ---------------------------------------------------------
// Render scheduling
//
// All parameter changes go through scheduleRender(), which
// batches updates via requestAnimationFrame. Before each
// render, we capture the viewport anchor and selection so
// they can be restored after the layout changes.
// ---------------------------------------------------------

function scheduleRender() {
  if (renderPending) return;
  renderPending = true;
  requestAnimationFrame(function() {
    renderPending = false;
    var anchor = computeAnchor();
    var ss = selToAddr();
    render(false);
    if (ss) addrToSel(ss);
    if (postRender) {
      postRender();
      postRender = null;
    } else if (anchor) {
      applyAnchor(anchor);
    }
  });
}

// Schedule a render that also scrolls to the start address
// (used when the user changes the start address).
function scheduleRenderAndFocus() {
  postRender = scrollToStart;
  scheduleRender();
}


// ---------------------------------------------------------
// File loading (button, drag-and-drop)
// ---------------------------------------------------------

function loadFile(file) {
  var reader = new FileReader();
  reader.onload = function() {
    fileData = new Uint8Array(reader.result);
    fileName = file.name;
    $('fileInfo').textContent = file.name + ' (' + fileData.length + ' bytes)';
    dropzone.classList.add('hidden');
    preview.classList.add('loaded');
    scheduleRender();
  };
  reader.readAsArrayBuffer(file);
}

$('btnOpen').addEventListener('click', function() { fileInput.click(); });
fileInput.addEventListener('change', function(e) {
  if (e.target.files[0]) loadFile(e.target.files[0]);
});

// Drag and drop on the whole page
document.body.addEventListener('dragover', function(e) {
  e.preventDefault();
  preview.classList.add('drag-over');
});
document.body.addEventListener('dragleave', function(e) {
  if (!e.relatedTarget || !document.body.contains(e.relatedTarget)) {
    preview.classList.remove('drag-over');
  }
});
document.body.addEventListener('drop', function(e) {
  e.preventDefault();
  preview.classList.remove('drag-over');
  if (e.dataTransfer.files[0]) loadFile(e.dataTransfer.files[0]);
});


// ---------------------------------------------------------
// Address navigation buttons
// ---------------------------------------------------------

function navAddr(delta) {
  var addr = Math.max(0, parseHex($('inStartAddr').value) + delta);
  $('inStartAddr').value = addr.toString(16);
  scheduleRenderAndFocus();
}

$('navPB').addEventListener('click', function() { navAddr(-1); });
$('navNB').addEventListener('click', function() { navAddr(1); });
$('navPS').addEventListener('click', function() {
  navAddr(-Math.max(1, getParams().frameStride));
});
$('navNS').addEventListener('click', function() {
  navAddr(Math.max(1, getParams().frameStride));
});


// ---------------------------------------------------------
// Control change listeners
// ---------------------------------------------------------

// Most controls trigger a re-render with viewport anchor
['inBpp', 'inEncoding', 'inWordSize', 'inByteOrder', 'inMsbFirst',
 'inWidth', 'inHeight', 'inCount', 'inRowStride', 'inFrameStride'
].forEach(function(id) {
  $(id).addEventListener('input', scheduleRender);
  $(id).addEventListener('change', scheduleRender);
});

// Start address changes also scroll to show the address
$('inStartAddr').addEventListener('input', scheduleRenderAndFocus);
$('inStartAddr').addEventListener('change', scheduleRenderAndFocus);

// Zoom via slider
$('inZoom').addEventListener('input', function() {
  doZoom(parseInt($('inZoom').value) || 2);
});

// Ctrl+wheel zoom
preview.addEventListener('wheel', function(e) {
  if (e.ctrlKey || e.metaKey) {
    e.preventDefault();
    var current = parseInt($('inZoom').value) || 2;
    doZoom(current + (e.deltaY < 0 ? 1 : -1));
  }
}, { passive: false });

// Re-render on window resize (column count may change)
window.addEventListener('resize', scheduleRender);
