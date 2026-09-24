const $ = (id) => document.getElementById(id);
const fileInput = $('file-input');
const dropzone = $('dropzone');
const status = $('status');
let currentFile = null;
let currentType = null;
let originalWidth = 0;
let originalHeight = 0;

function setStatus(message, kind = '') { status.textContent = message; status.className = `status ${kind}`; }
function formatType(type) { return {jpeg:'JPEG',png:'PNG',bmp:'BMP'}[type]; }
function typeFromBytes(data) {
  if (data[0] === 0xff && data[1] === 0xd8) return 'jpeg';
  if (data.length > 8 && data[0] === 137 && data[1] === 80 && data[2] === 78 && data[3] === 71 && data[4] === 13 && data[5] === 10 && data[6] === 26 && data[7] === 10) return 'png';
  if (data[0] === 66 && data[1] === 77) return 'bmp';
  throw new Error('This file is not a supported JPEG, PNG, or BMP image.');
}
function pixelsPerMetre(dpi) { return Math.round(dpi * 10000 / 254); }

function patchBmp(data, dpi) {
  if (data.length < 54 || data[0] !== 66 || data[1] !== 77) throw new Error('Invalid BMP file.');
  const view = new DataView(data.buffer, data.byteOffset, data.byteLength);
  if (view.getUint32(14, true) < 40) throw new Error('This older BMP header has no DPI fields. Choose PNG or JPEG output.');
  const result = data.slice(); const out = new DataView(result.buffer);
  out.setInt32(38, pixelsPerMetre(dpi), true); out.setInt32(42, pixelsPerMetre(dpi), true);
  return result;
}

const crcTable = new Uint32Array(256);
for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; crcTable[n] = c >>> 0; }
function crc32(data, start, end) { let c = 0xffffffff; for (let i = start; i < end; i++) c = crcTable[(c ^ data[i]) & 255] ^ (c >>> 8); return (c ^ 0xffffffff) >>> 0; }
function pngChunk(type, payload) {
  const chunk = new Uint8Array(payload.length + 12), v = new DataView(chunk.buffer);
  v.setUint32(0, payload.length); for (let i = 0; i < 4; i++) chunk[4+i] = type.charCodeAt(i);
  chunk.set(payload, 8); v.setUint32(chunk.length - 4, crc32(chunk, 4, chunk.length - 4)); return chunk;
}
function join(parts) { const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0)); let at = 0; for (const part of parts) { out.set(part, at); at += part.length; } return out; }
function patchPng(data, dpi) {
  if (typeFromBytes(data) !== 'png') throw new Error('Invalid PNG file.');
  const view = new DataView(data.buffer, data.byteOffset, data.byteLength);
  const density = new Uint8Array(9), dv = new DataView(density.buffer);
  dv.setUint32(0, pixelsPerMetre(dpi)); dv.setUint32(4, pixelsPerMetre(dpi)); density[8] = 1;
  const replacement = pngChunk('pHYs', density), parts = [data.subarray(0, 8)];
  let at = 8, inserted = false, ended = false;
  while (at + 12 <= data.length) {
    const len = view.getUint32(at), next = at + 12 + len;
    if (next > data.length) throw new Error('Invalid PNG chunk length.');
    const type = String.fromCharCode(...data.subarray(at + 4, at + 8));
    if (!inserted && (type === 'pHYs' || type === 'IDAT')) { parts.push(replacement); inserted = true; }
    if (type !== 'pHYs') parts.push(data.subarray(at, next));
    at = next; if (type === 'IEND') { ended = true; break; }
  }
  if (!ended || !inserted) throw new Error('Invalid PNG file structure.');
  if (at < data.length) parts.push(data.subarray(at));
  return join(parts);
}

function patchExif(data, segmentStart, segmentEnd, dpi) {
  if (segmentEnd - segmentStart < 16 || String.fromCharCode(...data.subarray(segmentStart, segmentStart + 6)) !== 'Exif\0\0') return;
  const base = segmentStart + 6, little = data[base] === 73 && data[base+1] === 73;
  if (!little && !(data[base] === 77 && data[base+1] === 77)) return;
  const v = new DataView(data.buffer, data.byteOffset, data.byteLength);
  const u16 = p => v.getUint16(p, little), u32 = p => v.getUint32(p, little);
  if (u16(base+2) !== 42) return;
  const ifd = base + u32(base+4); if (ifd + 2 > segmentEnd) return;
  const count = u16(ifd); if (count > 1024 || ifd + 2 + count*12 > segmentEnd) return;
  for (let n = 0; n < count; n++) {
    const p = ifd + 2 + n*12, tag = u16(p);
    if (tag === 0x0128 && u16(p+2) === 3 && u32(p+4) === 1) v.setUint16(p+8, 2, little);
    if ((tag === 0x011a || tag === 0x011b) && u16(p+2) === 5 && u32(p+4) === 1) {
      const at = base + u32(p+8);
      if (at + 8 <= segmentEnd) { v.setUint32(at, dpi, little); v.setUint32(at+4, 1, little); }
    }
  }
}
function patchJpeg(data, dpi) {
  if (typeFromBytes(data) !== 'jpeg') throw new Error('Invalid JPEG file.');
  const result = data.slice(), v = new DataView(result.buffer);
  let at = 2, jfif = false;
  while (at + 4 <= result.length && result[at] === 0xff) {
    let marker = result[at+1]; if (marker === 0xda || marker === 0xd9) break;
    if (marker === 0xff) { at++; continue; }
    if (marker === 0x01 || marker >= 0xd0 && marker <= 0xd7) { at += 2; continue; }
    const length = v.getUint16(at+2), end = at + 2 + length;
    if (length < 2 || end > result.length) throw new Error('Invalid JPEG segment.');
    const payload = at + 4;
    if (marker === 0xe0 && length >= 16 && String.fromCharCode(...result.subarray(payload,payload+5)) === 'JFIF\0') {
      result[payload+7] = 1; v.setUint16(payload+8, dpi); v.setUint16(payload+10, dpi); jfif = true;
    }
    if (marker === 0xe1) patchExif(result, payload, end, dpi);
    at = end;
  }
  if (jfif) return result;
  const segment = new Uint8Array([255,224,0,16,74,70,73,70,0,1,2,1,dpi>>8,dpi&255,dpi>>8,dpi&255,0,0]);
  return join([result.subarray(0,2),segment,result.subarray(2)]);
}
function patchMetadata(data, type, dpi) { return type === 'jpeg' ? patchJpeg(data,dpi) : type === 'png' ? patchPng(data,dpi) : patchBmp(data,dpi); }

async function decode(file) {
  if ('createImageBitmap' in window) return createImageBitmap(file);
  const url = URL.createObjectURL(file);
  try { const img = new Image(); img.src = url; await img.decode(); return img; }
  finally { URL.revokeObjectURL(url); }
}
function canvasBlob(canvas, type) { return new Promise((resolve,reject) => canvas.toBlob(blob => blob ? resolve(blob) : reject(new Error('The browser could not encode this image.')), type, .92)); }
function encodeBmp(canvas, dpi) {
  const {width:w,height:h} = canvas, rgba = canvas.getContext('2d').getImageData(0,0,w,h).data;
  const stride = (w*3+3)&~3, size = 54 + stride*h, bytes = new Uint8Array(size), v = new DataView(bytes.buffer);
  bytes[0] = 66; bytes[1] = 77; v.setUint32(2,size,true); v.setUint32(10,54,true); v.setUint32(14,40,true);
  v.setInt32(18,w,true); v.setInt32(22,h,true); v.setUint16(26,1,true); v.setUint16(28,24,true);
  v.setUint32(34,stride*h,true); v.setInt32(38,pixelsPerMetre(dpi),true); v.setInt32(42,pixelsPerMetre(dpi),true);
  for(let y=0;y<h;y++) for(let x=0;x<w;x++) { const s=(y*w+x)*4, d=54+(h-1-y)*stride+x*3, a=rgba[s+3]/255; bytes[d]=Math.round(rgba[s+2]*a+255*(1-a)); bytes[d+1]=Math.round(rgba[s+1]*a+255*(1-a)); bytes[d+2]=Math.round(rgba[s]*a+255*(1-a)); }
  return bytes;
}
async function renderPixels(file, width, height, type, dpi) {
  if (width*height > 32000000) throw new Error('The requested image exceeds this tool’s 32 million pixel processing limit.');
  const image = await decode(file);
  try {
    const canvas = document.createElement('canvas'); canvas.width=width; canvas.height=height;
    const ctx=canvas.getContext('2d',{willReadFrequently:type==='bmp'});
    if (!ctx) throw new Error('Canvas is unavailable in this browser.');
    if (type==='jpeg') { ctx.fillStyle='#fff'; ctx.fillRect(0,0,width,height); }
    ctx.imageSmoothingQuality='high'; ctx.drawImage(image,0,0,width,height);
    if (type==='bmp') return new Blob([encodeBmp(canvas,dpi)],{type:'image/bmp'});
    const blob=await canvasBlob(canvas,type==='png'?'image/png':'image/jpeg');
    const bytes=new Uint8Array(await blob.arrayBuffer());
    return new Blob([patchMetadata(bytes,type,dpi)],{type:type==='png'?'image/png':'image/jpeg'});
  } finally { if (image.close) image.close(); }
}
async function inspectFile(file) {
  if (!file) return;
  try {
    const type=typeFromBytes(new Uint8Array(await file.slice(0,16).arrayBuffer()));
    if (!['jpeg','png','bmp'].includes(type)) throw new Error('Unsupported image format.');
    const img=await decode(file); const w=img.width, h=img.height; if (img.close) img.close();
    if (!w || !h) throw new Error('Could not read the image dimensions.');
    currentFile=file; currentType=type; originalWidth=w; originalHeight=h;
    $('file-name').textContent=file.name; $('file-info').textContent=`${formatType(type)} · ${w} × ${h} px`;
    $('width-input').value=w; $('height-input').value=h; $('file-detail').hidden=false;
    $('convert-button').disabled=false; setStatus('Ready to convert.');
  } catch(error) { currentFile=null; $('convert-button').disabled=true; $('file-detail').hidden=true; setStatus(error.message,'error'); }
}
function syncMode() {
  const resize=document.querySelector('input[name="mode"]:checked').value==='resize';
  $('resize-fields').hidden=!resize;
  const format=$('output-format').value;
  $('format-note').textContent=resize ? 'Resizing redraws the image. Your selected DPI is written to the new file.' : format==='original' ? 'The original file type and pixel data are preserved; only the DPI metadata is changed.' : 'Changing the output format redraws the image, so pixels are re-encoded even in DPI tag mode.';
}
function syncPreset() { document.querySelectorAll('[data-dpi]').forEach(button=>button.classList.toggle('selected',button.dataset.dpi===$('dpi-input').value)); }
function triggerDownload(blob, name) { const url=URL.createObjectURL(blob), anchor=document.createElement('a'); anchor.href=url; anchor.download=name; document.body.append(anchor); anchor.click(); anchor.remove(); setTimeout(()=>URL.revokeObjectURL(url),60000); }

fileInput.addEventListener('change',()=>inspectFile(fileInput.files[0]));
for (const event of ['dragenter','dragover']) dropzone.addEventListener(event,e=>{e.preventDefault();dropzone.classList.add('dragging');});
for (const event of ['dragleave','drop']) dropzone.addEventListener(event,e=>{e.preventDefault();dropzone.classList.remove('dragging');});
dropzone.addEventListener('drop',e=>{if(e.dataTransfer.files.length!==1){setStatus('Choose only one image at a time.','error');return;}inspectFile(e.dataTransfer.files[0]);});
$('remove-file').addEventListener('click',()=>{fileInput.value='';currentFile=null;$('file-detail').hidden=true;$('convert-button').disabled=true;setStatus('Choose an image to get started.');});
document.querySelectorAll('[data-dpi]').forEach(button=>button.addEventListener('click',()=>{$('dpi-input').value=button.dataset.dpi;syncPreset();}));
$('dpi-input').addEventListener('input',syncPreset);
document.querySelectorAll('input[name="mode"]').forEach(input=>input.addEventListener('change',syncMode));
$('output-format').addEventListener('change',syncMode);
syncPreset();syncMode();
$('convert-button').addEventListener('click',async()=>{
  if(!currentFile)return;
  const dpi=Number($('dpi-input').value), width=Number($('width-input').value), height=Number($('height-input').value);
  if(!Number.isInteger(dpi)||dpi<1||dpi>65535){setStatus('Enter a whole-number DPI from 1 to 65535.','error');return;}
  const resize=document.querySelector('input[name="mode"]:checked').value==='resize';
  if(resize&&(!Number.isInteger(width)||!Number.isInteger(height)||width<1||height<1||width>16000||height>16000)){setStatus('Enter width and height between 1 and 16000 pixels.','error');return;}
  const type=$('output-format').value==='original'?currentType:$('output-format').value;
  const button=$('convert-button');button.disabled=true;setStatus('Processing locally…');
  try {
    let output;
    if(!resize&&type===currentType){const source=new Uint8Array(await currentFile.arrayBuffer());output=new Blob([patchMetadata(source,type,dpi)],{type:currentFile.type||`image/${type}`});}
    else output=await renderPixels(currentFile,resize?width:originalWidth,resize?height:originalHeight,type,dpi);
    const stem=currentFile.name.replace(/\.[^.]+$/,''); triggerDownload(output,`${stem}-${dpi}dpi.${{jpeg:'jpg',png:'png',bmp:'bmp'}[type]}`);
    setStatus(`Downloaded ${formatType(type)} at ${dpi} DPI. ${resize?`${width} × ${height} pixels.`:type===currentType?'Pixel data untouched.':'Output re-encoded.'}`,'success');
  } catch(error){setStatus(error.message||'Conversion failed.','error');}
  finally{button.disabled=false;}
});

export {patchJpeg,patchPng,patchBmp,typeFromBytes};
