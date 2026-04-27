
/* ════════════════════════════════════════════════════════════
   KND WAVES v5 — ULTRA PREMIUM EDITION
   KND Spatial Audio Engine · Canvas Visualizer
   Parallax · Smart Announcer · Hi-Fi DSP Chain
   ════════════════════════════════════════════════════════════ */

/* ── STATE ─────────────────────────────────────────────── */
const S={
  tracks:[], currentIdx:-1, upNext:[], playOrder:[],
  shuffle:false, repeatMode:'all', smartAutoplay:true, gaplessAutoplay:true, crossfade:true, smartColor:true, normalizeVolume:true, offlineLyrics:true,
  favorites:JSON.parse(localStorage.getItem('knd_fav')||'[]'),
  playCount:{}, history:[], lastSession:JSON.parse(localStorage.getItem('knd_last_session')||'null'), folderStats:JSON.parse(localStorage.getItem('knd_folder_stats')||'{}'),
  homeFilter:'all', libFilter:'all', libSort:'recent', libSearch:'',
  context:'KND WAVES', spatialMode:'spatial', remaster:false,
  accentR:0, accentG:217, accentB:255,
  tracksSinceLast:0,
  userName: localStorage.getItem('knd_user_name') || 'Dion Kennedy',
  themePref: localStorage.getItem('knd_theme') || 'auto'
};
function getInitials(name){
  const parts=(name||'').trim().split(/\s+/).filter(Boolean);
  if(!parts.length)return 'KW';
  if(parts.length===1)return parts[0].slice(0,2).toUpperCase();
  return (parts[0][0]+parts[parts.length-1][0]).toUpperCase();
}

/* ── DB ─────────────────────────────────────────────────── */
let db;
const DB='knd_v5', ST='tracks';
const openDB=()=>new Promise((ok,err)=>{const r=indexedDB.open(DB,1);r.onupgradeneeded=e=>{if(!e.target.result.objectStoreNames.contains(ST))e.target.result.createObjectStore(ST,{keyPath:'id'});};r.onsuccess=()=>{db=r.result;ok();};r.onerror=()=>err(r.error);});
const dbPut=t=>new Promise((ok,err)=>{const tx=db.transaction(ST,'readwrite');tx.objectStore(ST).put(t);tx.oncomplete=ok;tx.onerror=()=>err(tx.error);});
const dbAll=()=>new Promise((ok,err)=>{const tx=db.transaction(ST,'readonly');const r=tx.objectStore(ST).getAll();r.onsuccess=()=>ok(r.result||[]);r.onerror=()=>err(r.error);});
const dbDel=id=>new Promise((ok,err)=>{const tx=db.transaction(ST,'readwrite');tx.objectStore(ST).delete(id);tx.oncomplete=ok;tx.onerror=()=>err(tx.error);});
const dbClear=()=>new Promise((ok,err)=>{const tx=db.transaction(ST,'readwrite');tx.objectStore(ST).clear();tx.oncomplete=ok;tx.onerror=()=>err(tx.error);});

/* ── UTILS ──────────────────────────────────────────────── */
const $=s=>document.querySelector(s), $$=s=>[...document.querySelectorAll(s)];
const fmtT=s=>isFinite(s)?`${Math.floor(s/60)}:${String(Math.floor(s%60)).padStart(2,'0')}`:'0:00';
const fmtSz=b=>b<1e6?`${(b/1e3).toFixed(0)} KB`:`${(b/1e6).toFixed(1)} MB`;
const f2buf=f=>new Promise((ok,err)=>{const r=new FileReader();r.onload=()=>ok(r.result);r.onerror=err;r.readAsArrayBuffer(f);});
const f2url=f=>f?new Promise((ok,err)=>{const r=new FileReader();r.onload=()=>ok(r.result);r.onerror=err;r.readAsDataURL(f);}):Promise.resolve('');
const mkURL=t=>t.audioBuffer?URL.createObjectURL(new Blob([t.audioBuffer],{type:t.mimeType||'audio/mpeg'})):t.audioData||'';
const saveFavs=()=>localStorage.setItem('knd_fav',JSON.stringify(S.favorites));
const saveUsage=()=>localStorage.setItem('knd_usage',JSON.stringify({p:S.playCount,h:S.history.slice(0,80)}));
const saveLastSession=()=>{const a=$('#audio');const t=S.tracks[S.currentIdx];if(!a||!t)return;localStorage.setItem('knd_last_session',JSON.stringify({id:t.id,time:Math.max(0,a.currentTime||0),context:S.context,ts:Date.now()}));};
const saveFolderStats=()=>localStorage.setItem('knd_folder_stats',JSON.stringify(S.folderStats||{}));
const isFav=id=>S.favorites.includes(id);
function toast(msg,type='s'){const el=document.createElement('div');el.className=`toast ${type}`;el.textContent=msg;document.body.appendChild(el);setTimeout(()=>{el.style.opacity='0';el.style.transition='.35s';setTimeout(()=>el.remove(),350);},2700);}
function showConfirm(title,msg){return new Promise(res=>{$('#confirm-title').textContent=title;$('#confirm-msg').textContent=msg;$('#confirm-overlay').classList.add('on');$('#confirm-sheet').classList.add('on');const done=v=>{$('#confirm-overlay').classList.remove('on');$('#confirm-sheet').classList.remove('on');['#confirm-ok','#confirm-cancel'].forEach(s=>{const el=$(s);el.replaceWith(el.cloneNode(true));});res(v);};$('#confirm-ok').addEventListener('click',()=>done(true),{once:true});$('#confirm-cancel').addEventListener('click',()=>done(false),{once:true});$('#confirm-overlay').addEventListener('click',()=>done(false),{once:true});});}

/* ═══ KND SPATIAL AUDIO ENGINE ═══════════════════════════
   7-Band Parametric EQ + Harmonic Exciter + Compressor
   + Limiter + Real-time Analyser + Reverb
   ════════════════════════════════════════════════════════ */
let actx,srcNode,analyser,dataArr;
let nSub,nBass,nLmid,nMid,nHmid,nPresence,nAir;
let nExcIn,nExcWS,nExcGain,nComp,nLimiter,nDry,nWet,nConv,nMaster;
let visRAF=null,fadeBusy=false;

function makeImpulse(dur=2,dec=2.6){const r=actx.sampleRate,len=Math.floor(r*dur),b=actx.createBuffer(2,len,r);for(let c=0;c<2;c++){const d=b.getChannelData(c);for(let i=0;i<len;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/len,dec);}return b;}
function excCurve(a=2.5){const n=512,c=new Float32Array(n);for(let i=0;i<n;i++){const x=(i*2/n)-1;c[i]=Math.tanh(x*a);}return c;}

function initAudio(){
  if(actx)return;
  const audio=$('#audio');
  actx=new(window.AudioContext||window.webkitAudioContext)();
  srcNode=actx.createMediaElementSource(audio);
  // 7-Band EQ
  nSub=actx.createBiquadFilter();      nSub.type='lowshelf';  nSub.frequency.value=60;
  nBass=actx.createBiquadFilter();     nBass.type='lowshelf'; nBass.frequency.value=180;
  nLmid=actx.createBiquadFilter();     nLmid.type='peaking';  nLmid.frequency.value=500;  nLmid.Q.value=1.4;
  nMid=actx.createBiquadFilter();      nMid.type='peaking';   nMid.frequency.value=1200;  nMid.Q.value=1.2;
  nHmid=actx.createBiquadFilter();     nHmid.type='peaking';  nHmid.frequency.value=3500; nHmid.Q.value=1.1;
  nPresence=actx.createBiquadFilter(); nPresence.type='peaking'; nPresence.frequency.value=7000; nPresence.Q.value=0.9;
  nAir=actx.createBiquadFilter();      nAir.type='highshelf'; nAir.frequency.value=14000;
  // Harmonic Exciter
  nExcIn=actx.createGain();   nExcIn.gain.value=0.15;
  nExcWS=actx.createWaveShaper(); nExcWS.curve=excCurve(2.5); nExcWS.oversample='4x';
  nExcGain=actx.createGain(); nExcGain.gain.value=0.12;
  // Dynamics
  nComp=actx.createDynamicsCompressor(); nComp.threshold.value=-22; nComp.knee.value=18; nComp.ratio.value=3.5; nComp.attack.value=.003; nComp.release.value=.18;
  nLimiter=actx.createDynamicsCompressor(); nLimiter.threshold.value=-1.5; nLimiter.knee.value=0.5; nLimiter.ratio.value=20; nLimiter.attack.value=.001; nLimiter.release.value=.05;
  // Reverb
  nConv=actx.createConvolver(); nConv.buffer=makeImpulse();
  nDry=actx.createGain(); nDry.gain.value=1;
  nWet=actx.createGain(); nWet.gain.value=0.12;
  // Analyser
  analyser=actx.createAnalyser(); analyser.fftSize=512; analyser.smoothingTimeConstant=0.8;
  dataArr=new Uint8Array(analyser.frequencyBinCount);
  // Master
  nMaster=actx.createGain(); nMaster.gain.value=1;
  // Chain: src → EQ → exciter(||) → comp → reverb(||) → limiter → analyser → master → dest
  srcNode.connect(nSub); nSub.connect(nBass); nBass.connect(nLmid); nLmid.connect(nMid);
  nMid.connect(nHmid); nHmid.connect(nPresence); nPresence.connect(nAir);
  nAir.connect(nExcIn); nExcIn.connect(nExcWS); nExcWS.connect(nExcGain);
  nAir.connect(nComp); nExcGain.connect(nComp);
  nComp.connect(nDry); nComp.connect(nConv); nConv.connect(nWet);
  nDry.connect(nLimiter); nWet.connect(nLimiter);
  nLimiter.connect(analyser); analyser.connect(nMaster); nMaster.connect(actx.destination);
}
const resumeCtx=async()=>{if(actx?.state==='suspended')await actx.resume();};

/* ── EQ PRESETS ─────────────────────────────────────────── */
const PRESETS={
  flat:    {sub:0,  bass:0, lmid:0,  mid:0,  hmid:0,  pres:0, air:0,  exc:8,  wid:100,rev:8,  label:'Flat'},
  spatial: {sub:1.5,bass:2, lmid:-1, mid:1,  hmid:2,  pres:3, air:2,  exc:18, wid:140,rev:16, label:'KND Spatial'},
  hifi:    {sub:1,  bass:2, lmid:0,  mid:1,  hmid:3,  pres:4, air:4,  exc:14, wid:115,rev:12, label:'Hi-Fi'},
  bass:    {sub:8,  bass:6, lmid:2,  mid:0,  hmid:-1, pres:1, air:1,  exc:10, wid:110,rev:8,  label:'Deep Bass'},
  vocal:   {sub:-2, bass:-1,lmid:-2, mid:3,  hmid:4,  pres:5, air:3,  exc:12, wid:100,rev:14, label:'Vocal'},
  cinema:  {sub:3,  bass:4, lmid:0,  mid:-1, hmid:2,  pres:3, air:4,  exc:20, wid:160,rev:28, label:'Cinematic'}
};
function applyPreset(name){
  const p=PRESETS[name]||PRESETS.spatial;
  const m={sub:'#eq-sub',bass:'#eq-bass',lmid:'#eq-lmid',mid:'#eq-mid',hmid:'#eq-hmid',presence:'#eq-presence',air:'#eq-air',exciter:'#eq-exciter',width:'#eq-width',reverb:'#eq-reverb'};
  const vals={sub:p.sub,bass:p.bass,lmid:p.lmid,mid:p.mid,hmid:p.hmid,presence:p.pres,air:p.air,exciter:p.exc,width:p.wid,reverb:p.rev};
  Object.entries(m).forEach(([k,sel])=>{const el=$(sel);if(el)el.value=vals[k];});
  syncEQLabels(); if(actx)applyEQToNodes();
  S.spatialMode=name;
  const lbl=$('#spatial-badge-label');if(lbl)lbl.textContent=p.label;
  const badge=$('#eq-active-badge');if(badge)badge.textContent=p.label;
  $$('[data-preset]').forEach(b=>{b.classList.remove('on','on-gold');if(b.dataset.preset===name)b.classList.add(name==='spatial'||name==='cinema'?'on-gold':'on');});
}
function applyEQToNodes(){
  if(!actx)return;
  const g=id=>parseFloat($(id)?.value||0);
  nSub.gain.value=g('#eq-sub');nBass.gain.value=g('#eq-bass');nLmid.gain.value=g('#eq-lmid');
  nMid.gain.value=g('#eq-mid');nHmid.gain.value=g('#eq-hmid');nPresence.gain.value=g('#eq-presence');nAir.gain.value=g('#eq-air');
  const ev=g('#eq-exciter')/100;nExcIn.gain.value=ev*.2;nExcGain.gain.value=ev*.15;
  nWet.gain.value=g('#eq-reverb')/100;
}
function syncEQLabels(){
  const fmt=id=>{const v=parseFloat($(id)?.value||0);return(v>0?'+':'')+v+' dB';};
  const pct=id=>parseInt($(id)?.value||0)+'%';
  [['sub','#v-sub'],['bass','#v-bass'],['lmid','#v-lmid'],['mid','#v-mid'],['hmid','#v-hmid'],['presence','#v-presence'],['air','#v-air']].forEach(([k,s])=>{const el=$(s);if(el)el.textContent=fmt('#eq-'+k);});
  if($('#v-exciter'))$('#v-exciter').textContent=pct('#eq-exciter');
  if($('#v-width'))$('#v-width').textContent=pct('#eq-width');
  if($('#v-reverb'))$('#v-reverb').textContent=pct('#eq-reverb');
}

/* ── CANVAS SPECTRUM VISUALIZER ─────────────────────────── */
let cvs=null,cvCtx=null,annCvs=null,annCtx=null;
function initCanvas(){
  cvs=$('#vis-canvas');if(!cvs)return;cvCtx=cvs.getContext('2d');resizeCvs();
  annCvs=$('#announcer-canvas');if(annCvs)annCtx=annCvs.getContext('2d');
}
function resizeCvs(){if(!cvs)return;const w=cvs.parentElement;const dpr=window.devicePixelRatio||1;cvs.width=w.clientWidth*dpr;cvs.height=w.clientHeight*dpr;}
function drawSpectrum(){
  if(!cvs||!cvCtx||!analyser){visRAF=null;return;}
  visRAF=requestAnimationFrame(drawSpectrum);
  analyser.getByteFrequencyData(dataArr);
  const dpr=window.devicePixelRatio||1;
  const W=cvs.width/dpr,H=cvs.height/dpr;
  cvCtx.clearRect(0,0,cvs.width,cvs.height);
  cvCtx.save();cvCtx.scale(dpr,dpr);
  const bars=58,bw=(W-bars*1.5)/bars,gap=1.5;
  const {accentR:r,accentG:g,accentB:b}=S;
  for(let i=0;i<bars;i++){
    const fi=Math.floor(Math.pow(i/bars,1.6)*(dataArr.length*.72));
    const v=dataArr[fi]/255;
    const bh=Math.max(2,v*H*.92);
    const x=i*(bw+gap),y=H-bh;
    const gr=cvCtx.createLinearGradient(x,H,x,y);
    gr.addColorStop(0,`rgba(57,255,20,${.45+v*.55})`);
    gr.addColorStop(.5,`rgba(${r},${g},${b},${.6+v*.4})`);
    gr.addColorStop(1,`rgba(255,255,255,${.1+v*.55})`);
    cvCtx.fillStyle=gr;
    cvCtx.beginPath();
    if(cvCtx.roundRect)cvCtx.roundRect(x,y,bw,bh,2);else cvCtx.rect(x,y,bw,bh);
    cvCtx.fill();
    if(v>.62){cvCtx.shadowColor=`rgba(${r},${g},${b},.6)`;cvCtx.shadowBlur=8;cvCtx.fillRect(x,y,bw,2);cvCtx.shadowBlur=0;}
  }
  cvCtx.restore();
  // Announcer canvas
  if(annCtx&&annCvs&&$('#announcer-overlay').classList.contains('show')){
    const AW=annCvs.width,AH=annCvs.clientHeight||40;
    annCvs.width=annCvs.parentElement.clientWidth;annCvs.height=AH;
    annCtx.clearRect(0,0,annCvs.width,AH);
    const ab=Math.min(bars,24),abw=(annCvs.width-ab*2)/ab;
    for(let i=0;i<ab;i++){const fi=Math.floor(i/(ab-1)*(dataArr.length*.5));const av=dataArr[fi]/255;const abh=Math.max(2,av*AH*.9);const ax=i*(abw+2),ay=AH-abh;const agr=annCtx.createLinearGradient(ax,AH,ax,ay);agr.addColorStop(0,'rgba(255,209,102,.5)');agr.addColorStop(1,'rgba(255,209,102,.9)');annCtx.fillStyle=agr;annCtx.fillRect(ax,ay,abw,abh);}
  }
}
function startVis(){if(!visRAF&&analyser)drawSpectrum();}
function stopVis(){if(visRAF){cancelAnimationFrame(visRAF);visRAF=null;}if(cvCtx&&cvs)cvCtx.clearRect(0,0,cvs.width,cvs.height);}

/* ── DYNAMIC COLOR EXTRACTION ───────────────────────────── */
function extractColor(url){
  return new Promise(res=>{
    if(!url){res({r:0,g:217,b:255});return;}
    const img=new Image();img.crossOrigin='Anonymous';
    img.onload=()=>{
      const c=document.createElement('canvas');c.width=c.height=1;
      const cx=c.getContext('2d');cx.drawImage(img,0,0,1,1);
      const d=cx.getImageData(0,0,1,1).data;
      let r=d[0],g=d[1],b=d[2];
      const avg=(r+g+b)/3,f=1.75;
      r=Math.min(255,avg+(r-avg)*f);g=Math.min(255,avg+(g-avg)*f);b=Math.min(255,avg+(b-avg)*f);
      res({r:Math.round(r),g:Math.round(g),b:Math.round(b)});
    };img.onerror=()=>res({r:0,g:217,b:255});img.src=url;
  });
}
function applyAccent({r,g,b}){
  S.accentR=r;S.accentG=g;S.accentB=b;
  const el=document.documentElement;
  el.style.setProperty('--accent-r',r);el.style.setProperty('--accent-g',g);el.style.setProperty('--accent-b',b);
  el.style.setProperty('--accent',`rgb(${r},${g},${b})`);
  const mini=$('#mini-bar');if(mini)mini.style.borderColor=`rgba(${r},${g},${b},.18)`;
}

/* ══ KND WAVES ANNOUNCER (every 2 tracks) ═════════════════
   Uses Web Speech API + synthesised ambient tone
   ════════════════════════════════════════════════════════ */
let announcerBusy=false;

function synthesiseAmbient(){
  if(!actx)return null;
  const ctx2=new(window.AudioContext||window.webkitAudioContext)();
  const notes=[220,277.18,329.63,440];// Am chord
  const gains=[];
  notes.forEach((freq,i)=>{
    const osc=ctx2.createOscillator();
    const gain=ctx2.createGain();
    const pan=ctx2.createStereoPanner();
    osc.type=i%2===0?'sine':'triangle';
    osc.frequency.value=freq;
    pan.pan.value=(i-1.5)*.25;
    gain.gain.setValueAtTime(0,ctx2.currentTime);
    gain.gain.linearRampToValueAtTime(.055,ctx2.currentTime+1.2);
    gain.gain.setValueAtTime(.055,ctx2.currentTime+3);
    gain.gain.linearRampToValueAtTime(0,ctx2.currentTime+5);
    osc.connect(gain);gain.connect(pan);pan.connect(ctx2.destination);
    osc.start(ctx2.currentTime);osc.stop(ctx2.currentTime+5.5);
    gains.push(gain);
  });
  // subtle reverb on ambient
  const rev=ctx2.createConvolver();
  const buf=ctx2.createBuffer(2,ctx2.sampleRate*2,ctx2.sampleRate);
  for(let c=0;c<2;c++){const d=buf.getChannelData(c);for(let i=0;i<d.length;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/d.length,2.5);}
  rev.buffer=buf;
  setTimeout(()=>{try{ctx2.close();}catch(e){}},6000);
  return ctx2;
}

async function triggerAnnouncer(){
  if(announcerBusy||!('speechSynthesis' in window))return;
  announcerBusy=true;
  const overlay=$('#announcer-overlay');
  overlay.classList.add('show');
  // Pause main audio briefly
  const audio=$('#audio');const wasPlaying=!audio.paused;
  if(wasPlaying){audio.pause();}
  // Synthesised ambient
  const ambCtx=synthesiseAmbient();
  // Best voice selection
  const speak=()=>{
    const utt=new SpeechSynthesisUtterance('KND WAVES, sua nova experiência musical');
    utt.lang='pt-BR';utt.rate=0.82;utt.pitch=0.88;utt.volume=0.95;
    const voices=speechSynthesis.getVoices();
    const ptBR=voices.find(v=>v.lang==='pt-BR')||voices.find(v=>v.lang.startsWith('pt'))||voices.find(v=>v.lang.startsWith('en'));
    if(ptBR)utt.voice=ptBR;
    utt.onend=()=>{
      setTimeout(()=>{
        overlay.classList.remove('show');
        announcerBusy=false;
        if(wasPlaying)audio.play().catch(()=>{});
      },1200);
    };
    utt.onerror=()=>{overlay.classList.remove('show');announcerBusy=false;if(wasPlaying)audio.play().catch(()=>{});};
    speechSynthesis.speak(utt);
  };
  // Voices may need loading
  if(speechSynthesis.getVoices().length>0)speak();
  else speechSynthesis.addEventListener('voiceschanged',speak,{once:true});
}

/* ── PARALLAX ───────────────────────────────────────────── */
function updateParallax(){
  const hero=$('#parallax-hero');if(!hero)return;
  const bg=$('#ph-bg');if(!bg)return;
  const rect=hero.getBoundingClientRect();
  const ratio=Math.max(0,Math.min(1,-rect.top/(rect.height*.8)));
  bg.style.transform=`scale(1.3) translateY(${ratio*22}px)`;
}
window.addEventListener('scroll',updateParallax,{passive:true});

/* ── PLAYBACK ────────────────────────────────────────────── */
async function fadeIn(idx){
  if(fadeBusy)return;const track=S.tracks[idx];if(!track)return;
  fadeBusy=true;const audio=$('#audio');initAudio();await resumeCtx();
  const now=actx.currentTime;nMaster.gain.cancelScheduledValues(now);nMaster.gain.setValueAtTime(nMaster.gain.value,now);nMaster.gain.linearRampToValueAtTime(0,now+.25);
  await new Promise(r=>setTimeout(r,250));
  S.currentIdx=idx;audio.src=track._url;updateUI(track);applySmartVolume();
  audio.addEventListener('canplay',async function f(){
    audio.removeEventListener('canplay',f);
    try{await audio.play();bumpFolderStat(track);S.playCount[track.id]=(S.playCount[track.id]||0)+1;saveUsage();saveLastSession();preloadNextTrack();const t=actx.currentTime;nMaster.gain.cancelScheduledValues(t);nMaster.gain.setValueAtTime(0,t);nMaster.gain.linearRampToValueAtTime(1,t+.32);}catch(e){}
    fadeBusy=false;setPlayState(true);startVis();
  },{once:true});
}

async function playTrack(idx,ctx=''){
  const track=S.tracks[idx];if(!track)return;
  S.playCount[track.id]=(S.playCount[track.id]||0)+1;
  if(S.history[0]!==idx)S.history.unshift(idx);
  if(S.history.length>60)S.history.pop();
  if(ctx)S.context=ctx;
  try{localStorage.setItem('knd_usage',JSON.stringify({p:S.playCount,h:S.history}));}catch(e){}
  if($('#audio').src)await fadeIn(idx);
  else{S.currentIdx=idx;const a=$('#audio');a.src=track._url;initAudio();await resumeCtx();updateUI(track);applySmartVolume();try{await a.play();bumpFolderStat(track);S.playCount[track.id]=(S.playCount[track.id]||0)+1;saveUsage();saveLastSession();preloadNextTrack();setPlayState(true);startVis();}catch(e){}}
  showPage('player');
  // Announcer logic: every 2 tracks
  S.tracksSinceLast++;
  if(S.tracksSinceLast>=2){S.tracksSinceLast=0;setTimeout(triggerAnnouncer,1500);}
}
async function togglePlay(){
  const a=$('#audio');
  if(!a.src&&S.tracks.length){await playTrack(S.currentIdx>=0?S.currentIdx:0);return;}
  if(a.paused){try{initAudio();await resumeCtx();await a.play();startVis();}catch(e){}}
  else{a.pause();stopVis();}
}
function getSmartNextIndex(){return getSpotifyNextIndex();}
async function nextTrack(){const n=getSpotifyNextIndex();if(n<0){setPlayState(false);return;}await fadeIn(n);}
async function prevTrack(){
  if(!S.tracks.length)return;
  const a=$('#audio');if(a.currentTime>3){a.currentTime=0;return;}
  const h=S.history.find(i=>i!==S.currentIdx&&S.tracks[i]);
  if(typeof h==='number'){await fadeIn(h);return;}
  await fadeIn((S.currentIdx-1+S.tracks.length)%S.tracks.length);
}

/* ── UI UPDATE ───────────────────────────────────────────── */
function toggleFav(id){
  const i=S.favorites.indexOf(id);
  if(i>=0){S.favorites.splice(i,1);toast('Removida dos favoritos');}
  else{S.favorites.push(id);toast('♥ Adicionada aos favoritos');}
  saveFavs();updateFavUI();
}
function updateFavUI(){
  const t=S.tracks[S.currentIdx],on=!!(t&&isFav(t.id));
  const b=$('#player-fav');if(!b)return;
  b.classList.toggle('on',on);
  const p=b.querySelector('path');if(p)p.setAttribute('fill',on?'var(--accent)':'none');
}

async function updateUI(track){
  if(!track)return;
  $('#player-title').textContent=track.title;
  $('#player-artist').textContent=[track.project||null,track.genre||null].filter(Boolean).join(' · ')||'KND WAVES';
  $('#player-ctx').textContent=S.context||'KND WAVES';
  // Cover & ambient bg
  const cover=$('#player-cover'),fallback=$('#cover-fallback'),bg=$('#player-bg');
  if(track.coverUrl){
    cover.style.backgroundImage=`url(${track.coverUrl})`;cover.style.backgroundSize='cover';cover.style.backgroundPosition='center';
    if(fallback)fallback.style.display='none';
    if(bg)bg.style.backgroundImage=`url(${track.coverUrl})`;
    const color=await extractColor(track.coverUrl);applyAccent(color);
    // Update parallax hero
    $('#ph-bg').style.backgroundImage=`url(${track.coverUrl})`;
  }else{
    cover.style.backgroundImage='';if(fallback)fallback.style.display='flex';
    if(bg)bg.style.backgroundImage='none';
    applyAccent({r:0,g:217,b:255});
  }
  cover.classList.add('playing');
  updateFavUI();updateMini(track);updateMediaSession(track);
  // Update lyrics
  $('#lyrics-box').textContent=track.lyrics||'Sem letra adicionada ainda.';startSyncedLyrics(track);
  $('.track-row').forEach(r=>r.classList.toggle('playing',Number(r.dataset.trackIndex)===S.currentIdx));
}
function setPlayState(p){
  $('#ico-play').style.display=p?'none':'block';$('#ico-pause').style.display=p?'block':'none';
  $('#mini-ico-play').style.display=p?'none':'block';$('#mini-ico-pause').style.display=p?'block':'none';
  if(p)startVis();else stopVis();
}
function updateMini(track){
  const mp=$('#mini-bar');
  if(currentPage==='player'){mp.style.display='none';return;}
  mp.style.display='flex';
  $('#mini-title').textContent=track.title;
  $('#mini-sub').textContent=track.project||track.genre||'KND WAVES';
  const art=$('#mini-art');
  if(track.coverUrl){art.style.backgroundImage=`url(${track.coverUrl})`;art.style.backgroundSize='cover';art.innerHTML='';}
  else{art.style.backgroundImage='';art.innerHTML=`<div style="position:absolute;inset:0;display:grid;place-items:center"><div class="wb" style="height:16px;gap:2px"><span style="height:5px;width:3px;--d:1.3s;--dl:0s"></span><span style="height:12px;width:3px;--d:1.1s;--dl:.1s"></span><span style="height:8px;width:3px;--d:1.4s;--dl:.2s"></span><span style="height:13px;width:3px;--d:1.0s;--dl:.05s"></span></div></div>`;}
}
function updateMediaSession(track){
  if(!('mediaSession' in navigator)||!track)return;
  try{navigator.mediaSession.metadata=new MediaMetadata({title:track.title,artist:track.project||'KND WAVES',album:track.genre||'Local',artwork:track.coverUrl?[{src:track.coverUrl,sizes:'512x512',type:'image/jpeg'}]:[]});navigator.mediaSession.setActionHandler('play',togglePlay);navigator.mediaSession.setActionHandler('pause',togglePlay);navigator.mediaSession.setActionHandler('previoustrack',prevTrack);navigator.mediaSession.setActionHandler('nexttrack',nextTrack);}catch(e){}
}


/* ── PREMIUM OFFLINE INTELLIGENCE ───────────────────────── */
let nextPreload=null,nextPreloadIdx=-1,lyricsTimer=null;
function bumpFolderStat(track){const f=folderLabel(track);if(!f)return;const st=S.folderStats[f]||{plays:0,last:0};st.plays++;st.last=Date.now();S.folderStats[f]=st;saveFolderStats();}
function estimateTrackMood(track){const hay=((track.title||'')+' '+(track.project||'')+' '+(track.genre||'')+' '+(track.description||'')).toLowerCase();if(/worship|gospel|oração|cristo|deus|jesus|calm|ambient|lo-fi|lofi|piano/.test(hay))return 'calma';if(/trap|drill|phonk|hype|bass|808|rage|funk/.test(hay))return 'energia';if(/sad|dor|choro|saudade|noite|dark|melanc/.test(hay))return 'intensa';return 'equilibrada';}
function scoreNextCandidate(track,current){if(!track||!current||track.id===current.id)return -9999;let s=0;if(folderLabel(track)&&folderLabel(track)===folderLabel(current))s+=35;if(track.project&&track.project===current.project)s+=20;if(track.genre&&track.genre===current.genre)s+=15;if(isFav(track.id))s+=10;s+=(S.playCount[track.id]||0)*1.5;const age=Date.now()-(track.createdAt||0);if(age<1000*60*60*24*14)s+=4;if(S.history.slice(0,8).includes(S.tracks.indexOf(track)))s-=40;return s;}
function getSpotifyNextIndex(){if(S.upNext.length)return S.upNext.shift();if(!S.tracks.length)return -1;const cur=S.tracks[S.currentIdx];if(S.shuffle){let i;do{i=Math.floor(Math.random()*S.tracks.length)}while(i===S.currentIdx&&S.tracks.length>1);return i;}if(S.smartAutoplay&&cur){let best=-1,bestScore=-9999;S.tracks.forEach((t,i)=>{const sc=scoreNextCandidate(t,cur);if(sc>bestScore){bestScore=sc;best=i;}});if(best>=0&&bestScore>5)return best;}const n=S.currentIdx+1;if(n<S.tracks.length)return n;return S.repeatMode==='all'?0:-1;}
function preloadNextTrack(){const i=getSpotifyNextIndex();if(i<0||!S.tracks[i])return;if(nextPreloadIdx===i&&nextPreload)return;nextPreload=new Audio();nextPreload.preload='auto';nextPreload.src=S.tracks[i]._url;nextPreloadIdx=i;}
function parseLRC(text){const lines=[];(text||'').split(/\r?\n/).forEach(raw=>{const ms=[...raw.matchAll(/\[(\d{1,2}):(\d{2})(?:\.(\d{1,3}))?\]/g)];const lyric=raw.replace(/\[[^\]]+\]/g,'').trim();if(!ms.length||!lyric)return;ms.forEach(m=>lines.push({time:parseInt(m[1])*60+parseInt(m[2])+(parseInt((m[3]||'0').padEnd(3,'0'))/1000),text:lyric}));});return lines.sort((a,b)=>a.time-b.time);}
function readTextFile(file){return new Promise(ok=>{const r=new FileReader();r.onload=()=>ok(String(r.result||''));r.onerror=()=>ok('');r.readAsText(file);});}
function startSyncedLyrics(track){if(lyricsTimer)clearInterval(lyricsTimer);lyricsTimer=null;const lines=track?.lrcLines||parseLRC(track?.lyrics||'');if(!lines.length)return;const box=$('#lyrics-box');if(!box)return;lyricsTimer=setInterval(()=>{const a=$('#audio');if(!a||a.paused)return;let cur=lines[0];for(const l of lines){if(l.time<=a.currentTime+.15)cur=l;else break;}box.textContent=cur?.text||track.lyrics||'Sem letra adicionada ainda.';},320);}
function applySmartVolume(){const a=$('#audio');if(a)a.volume=S.normalizeVolume?.92:1;}
function announceCastStatus(msg,type='i'){const el=$('#cast-status');if(el){el.textContent=msg;el.classList.add('show');}toast(msg,type);}

/* ── ACTION SHEET ────────────────────────────────────────── */
let shIdx=-1;
function openSheet(idx){
  const t=S.tracks[idx];if(!t)return;shIdx=idx;
  const art=$('#sheet-art');
  if(t.coverUrl){art.style.backgroundImage=`url(${t.coverUrl})`;art.style.backgroundSize='cover';art.innerHTML='';}
  else{art.style.backgroundImage='';art.innerHTML=wbMini();}
  $('#sheet-title').textContent=t.title;$('#sheet-sub').textContent=[t.project,t.genre].filter(Boolean).join(' · ')||'KND WAVES';
  const f=isFav(t.id);$('#sh-fav').classList.toggle('fav-on',f);$('#sh-fav-label').textContent=f?'Remover dos favoritos':'Favoritar';
  $('#sheet-overlay').classList.add('on');$('#action-sheet').classList.add('on');
}
function closeSheet(){$('#sheet-overlay').classList.remove('on');$('#action-sheet').classList.remove('on');}
const wbMini=()=>`<div style="position:absolute;inset:0;display:grid;place-items:center"><div class="wb" style="height:18px;gap:2px"><span style="height:6px;width:3px;--d:1.3s;--dl:0s"></span><span style="height:14px;width:3px;--d:1.1s;--dl:.1s"></span><span style="height:9px;width:3px;--d:1.4s;--dl:.2s"></span><span style="height:16px;width:3px;--d:1.0s;--dl:.05s"></span></div></div>`;

/* ── EDIT MODAL ──────────────────────────────────────────── */
let editId=null;
function openEdit(idx){closeSheet();const t=S.tracks[idx];if(!t)return;editId=t.id;$('#edit-title').value=t.title||'';$('#edit-project').value=t.project||'';$('#edit-genre').value=t.genre||'Eletrônico';$('#edit-lyrics').value=t.lyrics||'';$('#modal-overlay').classList.add('on');$('#edit-modal').classList.add('on');setTimeout(()=>$('#edit-title').focus(),200);}
function closeEdit(){$('#modal-overlay').classList.remove('on');$('#edit-modal').classList.remove('on');editId=null;}
async function saveEdit(){
  if(!editId)return;const t=S.tracks.find(x=>x.id===editId);if(!t)return;
  const ti=$('#edit-title').value.trim();if(!ti){toast('Título não pode ser vazio','e');return;}
  t.title=ti;t.project=$('#edit-project').value.trim();t.genre=$('#edit-genre').value;t.lyrics=$('#edit-lyrics').value.trim();
  try{await dbPut(t);await loadTracks();closeEdit();toast('Faixa atualizada ✓');if(S.tracks[S.currentIdx]?.id===t.id)updateUI(S.tracks[S.currentIdx]);}catch(e){toast('Erro ao salvar','e');}
}
async function deleteTrack(idx){
  const t=S.tracks[idx];if(!t)return;closeSheet();
  const ok=await showConfirm('Excluir faixa',`"${t.title}" será removida permanentemente.`);if(!ok)return;
  try{await dbDel(t.id);if(t._url?.startsWith('blob:'))URL.revokeObjectURL(t._url);const fi=S.favorites.indexOf(t.id);if(fi>=0){S.favorites.splice(fi,1);saveFavs();}if(S.currentIdx===idx){$('#audio').pause();$('#audio').src='';S.currentIdx=-1;setPlayState(false);stopVis();}else if(S.currentIdx>idx)S.currentIdx--;await loadTracks();toast('Faixa excluída');}catch(e){toast('Erro ao excluir','e');}
}

/* ── QUEUE ───────────────────────────────────────────────── */
function openQueue(){renderQueue();$('#queue-overlay').classList.add('on');$('#queue-sheet').classList.add('on');$('#queue-ctx-name').textContent=S.context||'Sua biblioteca';$('#qf-shuffle').classList.toggle('on-g',S.shuffle);const rm={off:'Repetir',all:'Repetir tudo',one:'Repetir 1'};$('#qf-rpt-label').textContent=rm[S.repeatMode];$('#qf-repeat').classList.toggle('on',S.repeatMode!=='off');}
function closeQueue(){$('#queue-overlay').classList.remove('on');$('#queue-sheet').classList.remove('on');}
function qArt(t){const el=document.createElement('div');el.className='q-art';if(t.coverUrl){el.style.backgroundImage=`url(${t.coverUrl})`;el.style.backgroundSize='cover';}else el.innerHTML=wbMini();return el;}
function renderQueue(){
  const list=$('#queue-list');list.innerHTML='';
  const cur=S.tracks[S.currentIdx];
  if(cur){const s=document.createElement('div');s.className='qs-label';s.textContent='Tocando agora';list.appendChild(s);const row=document.createElement('div');row.className='q-track cur';row.appendChild(qArt(cur));const meta=document.createElement('div');meta.className='q-meta';meta.innerHTML=`<div class="q-title play truncate">${cur.title}</div><div class="q-sub truncate">${cur.project||cur.genre||'—'}</div>`;const pb=document.createElement('button');pb.className='q-btn';pb.innerHTML=$('#audio').paused?'<svg width="14" height="14" fill="currentColor" viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>':'<svg width="14" height="14" fill="currentColor" viewBox="0 0 24 24"><path d="M6 19h4V5H6v14zm8-14v14h4V5h-4z"/></svg>';pb.onclick=e=>{e.stopPropagation();togglePlay();};row.appendChild(meta);row.appendChild(pb);list.appendChild(row);}
  if(S.upNext.length){const s=document.createElement('div');s.className='qs-label';s.textContent='A seguir';list.appendChild(s);S.upNext.forEach((ti,i)=>{const t=S.tracks[ti];if(!t)return;const row=document.createElement('div');row.className='q-track';row.appendChild(qArt(t));const meta=document.createElement('div');meta.className='q-meta';meta.innerHTML=`<div class="q-title truncate">${t.title}</div><div class="q-sub truncate">${t.project||t.genre||'—'}</div>`;const rb=document.createElement('button');rb.className='q-btn';rb.innerHTML='<svg width="13" height="13" fill="none" viewBox="0 0 24 24"><path d="M18 6L6 18M6 6l12 12" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg>';rb.onclick=e=>{e.stopPropagation();S.upNext.splice(i,1);renderQueue();};row.appendChild(meta);row.appendChild(rb);row.addEventListener('click',()=>{const si=S.upNext.splice(i,1)[0];playTrack(si);closeQueue();});list.appendChild(row);});}
  if(S.tracks.length>1){const s=document.createElement('div');s.className='qs-label';s.textContent='Próximas';list.appendChild(s);for(let i=0;i<Math.min(8,S.tracks.length-1);i++){const ni=(S.currentIdx+1+i)%S.tracks.length;if(ni===S.currentIdx)continue;const t=S.tracks[ni];const row=document.createElement('div');row.className='q-track';row.appendChild(qArt(t));const meta=document.createElement('div');meta.className='q-meta';meta.innerHTML=`<div class="q-title truncate">${t.title}</div><div class="q-sub truncate">${t.project||t.genre||'—'}</div>`;row.appendChild(meta);row.addEventListener('click',()=>{playTrack(ni);closeQueue();});list.appendChild(row);}}
  if(!cur&&!S.tracks.length)list.innerHTML='<div class="empty-state"><div class="empty-icon"><svg width="22" height="22" fill="none" viewBox="0 0 24 24"><path d="M4 6h16M4 12h16M4 18h6" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/></svg></div><div class="empty-title">Fila vazia</div></div>';
}

/* ── GENRE COLORS ────────────────────────────────────────── */
const GC={'Eletrônico':['#39ff14','#003310'],'Trap':['#ff6b35','#1a0800'],'Ambient':['#00bfae','#002e2a'],'Worship':['#9b59b6','#240035'],'Alt Pop':['#e91e8c','#380025'],'Hip Hop':['#ff8c00','#1f1000'],'R&B':['#c2185b','#180010'],'Lo-Fi':['#6d9b6d','#0b1a0b'],'Phonk':['#cc2200','#150000'],'Drill':['#3949ab','#040830'],'Gospel':['#f9a825','#180f00'],'Outro':['#546e7a','#080e10']};

/* ── RENDER HELPERS ──────────────────────────────────────── */
function makeArt(url,size=52,radius=13){
  const el=document.createElement('div');el.className='track-art';el.style.cssText=`width:${size}px;height:${size}px;border-radius:${radius}px;flex-shrink:0`;
  if(url){el.style.backgroundImage=`url(${url})`;el.style.backgroundSize='cover';el.style.backgroundPosition='center';}
  else el.innerHTML=`<div style="position:absolute;inset:0;display:grid;place-items:center"><div class="wb" style="height:${Math.round(size*.5)}px;gap:2px"><span style="height:${Math.round(size*.13)}px;width:3px;--d:1.3s;--dl:0s"></span><span style="height:${Math.round(size*.27)}px;width:3px;--d:1.1s;--dl:.1s"></span><span style="height:${Math.round(size*.18)}px;width:3px;--d:1.4s;--dl:.2s"></span><span style="height:${Math.round(size*.32)}px;width:3px;--d:1.0s;--dl:.05s"></span></div></div>`;
  const now=document.createElement('div');now.className='track-art-now';now.innerHTML=`<div class="wb" style="height:13px;gap:2px"><span style="height:4px;width:3px;--d:1.3s;--dl:0s"></span><span style="height:10px;width:3px;--d:1.1s;--dl:.1s"></span><span style="height:6px;width:3px;--d:1.4s;--dl:.2s"></span><span style="height:12px;width:3px;--d:1.0s;--dl:.05s"></span></div>`;
  el.appendChild(now);return el;
}

function makeTrackRow(track,idx){
  const row=document.createElement('div');row.className='track-row';row.dataset.trackIndex=String(idx);if(idx===S.currentIdx)row.classList.add('playing');
  const art=makeArt(track.coverUrl,52,13);
  const meta=document.createElement('div');meta.className='track-meta';meta.innerHTML=`<div class="track-title truncate">${track.title}</div><div class="track-sub truncate">${[track.project||null,track.genre||null].filter(Boolean).join(' · ')||'—'}</div>`;
  const more=document.createElement('button');more.className='more-btn';more.innerHTML='<svg width="15" height="15" fill="none" viewBox="0 0 24 24"><circle cx="12" cy="5" r="1.5" fill="currentColor"/><circle cx="12" cy="12" r="1.5" fill="currentColor"/><circle cx="12" cy="19" r="1.5" fill="currentColor"/></svg>';
  more.onclick=e=>{e.stopPropagation();openSheet(idx);};
  row.appendChild(art);row.appendChild(meta);row.appendChild(more);
  row.addEventListener('click',()=>playTrack(idx,S.context));
  return row;
}

/* ── RENDER PAGES ────────────────────────────────────────── */
function renderFeatured(){
  const c=$('#featured-cards');c.innerHTML='';
  const items=S.tracks.slice(0,6);
  // Always render at least 3 cards to keep layout balanced — fill with placeholders if needed
  const minCards=3;
  const placeholderTitles=['Adicione mais','Sua próxima','Em breve','Seu projeto','Novo som','Vibe KND'];
  const total=Math.max(items.length,minCards);

  for(let i=0;i<total;i++){
    const t=items[i];
    const card=document.createElement('div');
    card.className='tcard'+(t?'':' placeholder');
    const art=document.createElement('div');art.className='tcard-art';
    if(t&&t.coverUrl){
      art.style.backgroundImage=`url(${t.coverUrl})`;
      art.style.backgroundSize='cover';art.style.backgroundPosition='center';
    } else {
      art.innerHTML=`<div style="position:absolute;inset:0;display:grid;place-items:center"><div class="wb" style="height:30px;gap:3px"><span style="height:9px;width:4px;--d:1.3s;--dl:0s"></span><span style="height:22px;width:4px;--d:1.1s;--dl:.1s"></span><span style="height:15px;width:4px;--d:1.4s;--dl:.2s"></span><span style="height:26px;width:4px;--d:1.0s;--dl:.05s"></span></div></div>`;
    }
    card.appendChild(art);
    const title=t?t.title:placeholderTitles[i%placeholderTitles.length];
    const sub=t?(t.project||t.genre||'—'):'KND WAVES';
    card.innerHTML+=`<div class="tcard-info"><div class="tcard-title truncate">${title}</div><div class="tcard-sub truncate">${sub}</div></div>`;
    if(t){
      const idx=items.indexOf(t);
      card.addEventListener('click',()=>playTrack(idx,'Destaques'));
    } else {
      card.addEventListener('click',()=>showPage('upload'));
    }
    c.appendChild(card);
  }
}

function renderRecents(){
  const c=$('#home-recents'),wrap=$('#home-recents-wrap');
  const recent=S.history.slice(0,6).map(i=>S.tracks[i]).filter(Boolean);
  if(!recent.length){if(wrap)wrap.style.display='none';return;}
  if(wrap)wrap.style.display='block';c.innerHTML='';
  recent.forEach(t=>{const idx=S.tracks.indexOf(t);const item=document.createElement('div');item.className='recent-item';const art=document.createElement('div');art.className='recent-art';if(t.coverUrl){art.style.backgroundImage=`url(${t.coverUrl})`;art.style.backgroundSize='cover';}else art.innerHTML=wbMini();const name=document.createElement('div');name.className='recent-name';name.textContent=t.title;item.appendChild(art);item.appendChild(name);item.addEventListener('click',()=>playTrack(idx,'Recentes'));c.appendChild(item);});
}

function renderContinue(){
  const c=$('#continue-listening');c.innerHTML='';
  const recent=S.history.slice(0,3).map(i=>S.tracks[i]).filter(Boolean);
  if(!recent.length){c.innerHTML='<div style="padding:4px 0 14px;color:var(--muted);font-size:.78rem">Nenhuma música ouvida ainda.</div>';return;}
  recent.forEach(t=>{const idx=S.tracks.indexOf(t);c.appendChild(makeTrackRow(t,idx));});
}

function renderHomeFavs(){
  const c=$('#continue-listening');c.innerHTML='';
  const favs=S.tracks.filter(t=>isFav(t.id));
  if(!favs.length){c.innerHTML='<div class="empty-state"><div class="empty-icon"><svg width="22" height="22" fill="none" viewBox="0 0 24 24"><path d="M12 21.35l-1.45-1.32C5.4 15.36 2 12.28 2 8.5 2 5.42 4.42 3 7.5 3c1.74 0 3.41.81 4.5 2.09C13.09 3.81 14.76 3 16.5 3 19.58 3 22 5.42 22 8.5c0 3.78-3.4 6.86-8.55 11.54L12 21.35z" stroke="currentColor" stroke-width="1.8"/></svg></div><div class="empty-title">Sem favoritas ainda</div><div class="empty-sub">Toque no ♥ no player para favoritar.</div></div>';return;}
  favs.forEach(t=>{const idx=S.tracks.indexOf(t);c.appendChild(makeTrackRow(t,idx));});
}

function folderLabel(t){return (t.importFolder||((t.folderPath||'').includes('/')?(t.folderPath||'').split('/')[0]:'' )||'').trim();}
function makeFolderLibraryGroup(folder,tracks){
  const group=document.createElement('section');group.className='folder-library-group';
  const head=document.createElement('div');head.className='folder-library-head';
  head.innerHTML='<div class="folder-library-icon"><svg width="23" height="23" fill="none" viewBox="0 0 24 24"><path d="M3 7.5A2.5 2.5 0 0 1 5.5 5H10l2 2h6.5A2.5 2.5 0 0 1 21 9.5v7A2.5 2.5 0 0 1 18.5 19h-13A2.5 2.5 0 0 1 3 16.5v-9z" stroke="currentColor" stroke-width="1.8" stroke-linejoin="round"/></svg></div><div class="folder-library-meta"><div class="folder-library-kicker">Pasta na biblioteca</div><div class="folder-library-name"></div><div class="folder-library-count"></div></div><div class="folder-library-actions"><button class="folder-play-btn" type="button" aria-label="Tocar pasta"><svg width="18" height="18" fill="currentColor" viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg></button></div>';
  head.querySelector('.folder-library-name').textContent=folder;
  head.querySelector('.folder-library-count').textContent=tracks.length===1?'1 música dentro desta pasta':tracks.length+' músicas dentro desta pasta';
  const badges=document.createElement('div');badges.className='smart-badges';badges.innerHTML='<span class="smart-badge">Autoplay</span><span class="smart-badge">Fila inteligente</span><span class="smart-badge">Cast ready</span>';
  const body=document.createElement('div');body.className='folder-library-tracks';
  tracks.forEach(t=>{const idx=S.tracks.indexOf(t);body.appendChild(makeTrackRow(t,idx));});
  head.querySelector('.folder-play-btn').addEventListener('click',e=>{e.stopPropagation();const first=tracks[0];if(!first)return;S.context=folder;S.repeatMode='all';S.smartAutoplay=true;const idx=S.tracks.indexOf(first);playTrack(idx,folder);});
  group.appendChild(head);group.appendChild(badges);group.appendChild(body);return group;
}
function renderLibrary(){
  const lib=$('#lib-list');lib.innerHTML='';
  let list=S.tracks.slice();
  if(S.libFilter==='favorites')list=list.filter(t=>isFav(t.id));
  else if(S.libFilter!=='all')list=list.filter(t=>t.genre===S.libFilter);
  if(S.libSearch){const q=S.libSearch.toLowerCase();list=list.filter(t=>(t.title+' '+(t.project||'')+' '+(t.genre||'')+' '+folderLabel(t)).toLowerCase().includes(q));}
  if(S.libSort==='az')list.sort((a,b)=>a.title.localeCompare(b.title));
  const lbl=$('#lib-count');if(lbl)lbl.textContent=list.length===1?'1 música':`${list.length} músicas`;
  const sc=$('#s-track-count');if(sc)sc.textContent=S.tracks.length===1?'1 faixa':`${S.tracks.length} faixas`;
  if(!list.length){lib.innerHTML=`<div class="empty-state"><div class="empty-icon"><svg width="24" height="24" fill="none" viewBox="0 0 24 24"><path d="M9 18V5l12-2v13" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/><circle cx="6" cy="18" r="3" stroke="currentColor" stroke-width="1.8"/><circle cx="18" cy="16" r="3" stroke="currentColor" stroke-width="1.8"/></svg></div><div class="empty-title">Nenhuma faixa</div><div class="empty-sub">${S.libFilter==='favorites'?'Favorite faixas no player.':'Adicione músicas na aba Upload.'}</div></div>`;return;}
  const folders=new Map(),loose=[];
  list.forEach(t=>{const f=folderLabel(t);if(f){if(!folders.has(f))folders.set(f,[]);folders.get(f).push(t);}else loose.push(t);});
  folders.forEach((tracks,folder)=>lib.appendChild(makeFolderLibraryGroup(folder,tracks)));
  if(loose.length&&folders.size){const title=document.createElement('div');title.className='library-standalone-title';title.textContent='Músicas soltas';lib.appendChild(title);}
  loose.forEach(t=>{const idx=S.tracks.indexOf(t);lib.appendChild(makeTrackRow(t,idx));});
}function renderLibTabs(){
  $$('.filter-tab[data-lg]').forEach(t=>t.remove());
  const genres=[...new Set(S.tracks.map(t=>t.genre).filter(Boolean))];
  const tabs=$('#lib-filter-tabs');
  genres.forEach(g=>{const btn=document.createElement('button');btn.className='filter-tab';btn.dataset.lf=g;btn.dataset.lg='1';btn.textContent=g;btn.addEventListener('click',()=>{S.libFilter=g;$$('.filter-tab').forEach(t=>t.classList.remove('on'));btn.classList.add('on');renderLibrary();});tabs.appendChild(btn);});
}

function renderSearch(query='',genre=''){
  const empty=$('#search-empty'),results=$('#search-results');
  if(!query&&!genre){empty.classList.remove('hidden');results.classList.add('hidden');renderGenreGrid();return;}
  empty.classList.add('hidden');results.classList.remove('hidden');results.innerHTML='';
  let items=S.tracks;
  if(genre)items=items.filter(t=>t.genre===genre);
  if(query){const q=query.toLowerCase();items=items.filter(t=>(t.title+' '+(t.project||'')+' '+(t.genre||'')).toLowerCase().includes(q));}
  if(!items.length){results.innerHTML='<div class="empty-state"><div class="empty-icon"><svg width="22" height="22" fill="none" viewBox="0 0 20 20"><circle cx="9" cy="9" r="6.5" stroke="currentColor" stroke-width="1.8"/><path d="M14.5 14.5L18 18" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/></svg></div><div class="empty-title">Nenhum resultado</div></div>';return;}
  items.forEach(t=>{const idx=S.tracks.indexOf(t);results.appendChild(makeTrackRow(t,idx));});
}

function renderGenreGrid(){
  const grid=$('#genre-grid');grid.innerHTML='';
  const genres=[...new Set(S.tracks.map(t=>t.genre).filter(Boolean))];
  if(!genres.length){grid.innerHTML='<div style="color:var(--muted);font-size:.8rem">Adicione músicas para ver gêneros aqui.</div>';return;}
  genres.forEach(g=>{const colors=GC[g]||['#546e7a','#080e10'];const count=S.tracks.filter(t=>t.genre===g).length;const card=document.createElement('div');card.className='genre-card';card.style.background=`linear-gradient(135deg,${colors[0]},${colors[1]})`;card.innerHTML=`<div class="genre-card-name">${g}</div><div class="genre-card-count">${count} faixa${count!==1?'s':''}</div>`;const deco=document.createElement('div');deco.className='genre-deco';deco.style.background=`linear-gradient(135deg,${colors[0]}80,${colors[1]})`;card.appendChild(deco);card.addEventListener('click',()=>{$('#page-search-input').value=g;renderSearch('',g);});grid.appendChild(card);});
}

function updateHero(){
  const t=S.tracks[0];
  $('#ph-title').innerHTML=t?t.title:`<span class="grad">KND</span> WAVES`;
  $('#ph-sub').textContent=t?(t.description||t.project||'Sua música. Seu espaço.'):'Sua biblioteca musical privada.';
  if(t?.coverUrl)$('#ph-bg').style.backgroundImage=`url(${t.coverUrl})`;
}

/* ── PAGE NAV ─────────────────────────────────────────────── */
let currentPage='home',prevPage='home';
function showPage(id){
  if(id!=='player')prevPage=currentPage;
  $$('.page').forEach(p=>{if(p.id==='page-player')return;p.classList.toggle('active',p.id===`page-${id}`);});
  $$('.nav-tab').forEach(t=>t.classList.toggle('on',t.dataset.tab===id));
  currentPage=id;
  const onP=(id==='player');
  document.body.classList.toggle('player-open',onP);
  $('#page-player').classList.toggle('active',onP);
  const mini=$('#mini-bar');if(mini)mini.style.display=onP?'none':(S.currentIdx>=0?'flex':'none');
  if(onP){initCanvas();resizeCvs();if(!$('#audio').paused)startVis();}else stopVis();
  if(id==='home'){if(S.homeFilter==='all'){renderRecents();renderContinue();renderFeatured();}else renderHomeFavs();updateHero();}
  if(id==='library'){renderLibrary();renderLibTabs();}
  if(id==='search'){renderSearch($('#page-search-input').value);renderGenreGrid();}
  if(id!=='player')window.scrollTo({top:0,behavior:'smooth'});
}

/* ── PROGRESS & SCRUB ─────────────────────────────────────── */
let scrubbing=false;
function bindProgress(){
  const track=$('#prog-track');
  const seek=e=>{const a=$('#audio');if(!a.duration)return;const rect=track.getBoundingClientRect();const x=(e.touches?e.touches[0].clientX:e.clientX)-rect.left;const pct=Math.max(0,Math.min(1,x/rect.width));a.currentTime=pct*a.duration;$('#prog-fill').style.width=(pct*100)+'%';$('#mini-prog-fill').style.width=(pct*100)+'%';};
  track.addEventListener('pointerdown',e=>{scrubbing=true;seek(e);track.setPointerCapture(e.pointerId);});
  track.addEventListener('pointermove',e=>{if(scrubbing)seek(e);});
  track.addEventListener('pointerup',()=>{scrubbing=false;});
}

/* -- FOLDER IMPORT + BASIC LOCAL METADATA ------------------- */
const AUDIO_EXTS=['mp3','m4a','aac','wav','ogg','opus','flac','webm'];
const cleanName=name=>(name||'').replace(/\.[^.]+$/,'').replace(/[._-]+/g,' ').replace(/\s+/g,' ').trim();
function isAudioFile(file){const ext=(file.name.split('.').pop()||'').toLowerCase();return file.type.startsWith('audio/')||AUDIO_EXTS.includes(ext);}
function syncSafeInt(bytes){return bytes.reduce((n,b)=>(n<<7)|(b&0x7f),0);}
function readTextFrame(view,start,size){
  if(size<=1)return '';
  const enc=view.getUint8(start),bytes=new Uint8Array(view.buffer,start+1,size-1);
  try{
    if(enc===1||enc===2){const be=enc===2;let out='';for(let i=0;i+1<bytes.length;i+=2){const c=be?(bytes[i]<<8|bytes[i+1]):(bytes[i+1]<<8|bytes[i]);if(c)out+=String.fromCharCode(c);}return out.replace(/\0/g,'').trim();}
    return new TextDecoder(enc===3?'utf-8':'iso-8859-1').decode(bytes).replace(/\0/g,'').trim();
  }catch(e){return '';}
}
async function readLocalMetadata(file){
  const meta={title:cleanName(file.name),project:'',album:'',coverUrl:''};
  try{
    const buf=await file.slice(0,1024*1024).arrayBuffer();const view=new DataView(buf);
    if(view.byteLength<10||String.fromCharCode(...new Uint8Array(buf,0,3))!=='ID3')return meta;
    const major=view.getUint8(3);const tagSize=syncSafeInt([view.getUint8(6),view.getUint8(7),view.getUint8(8),view.getUint8(9)]);
    let off=10,end=Math.min(view.byteLength,10+tagSize);
    while(off+10<=end){
      const id=String.fromCharCode(...new Uint8Array(buf,off,4));if(!/^[A-Z0-9]{4}$/.test(id))break;
      const size=major===4?syncSafeInt([view.getUint8(off+4),view.getUint8(off+5),view.getUint8(off+6),view.getUint8(off+7)]):view.getUint32(off+4);
      const data=off+10;if(size<=0||data+size>view.byteLength)break;
      if(id==='TIT2')meta.title=readTextFrame(view,data,size)||meta.title;
      if(id==='TPE1')meta.project=readTextFrame(view,data,size)||meta.project;
      if(id==='TALB')meta.album=readTextFrame(view,data,size)||meta.album;
      if(id==='APIC'&&!meta.coverUrl){let p=data+1;while(p<data+size&&view.getUint8(p)!==0)p++;const mime=new TextDecoder('iso-8859-1').decode(new Uint8Array(buf,data+1,Math.max(0,p-data-1)))||'image/jpeg';p+=2;while(p<data+size&&view.getUint8(p)!==0)p++;p++;if(p<data+size){const pic=new Uint8Array(buf,p,data+size-p);meta.coverUrl=URL.createObjectURL(new Blob([pic],{type:mime}));}}
      off=data+size;
    }
  }catch(e){}
  return meta;
}
const KND_MAX_IMPORT_FILES=30;

function kndSetImportPanelState(type,folder,tracks,message){
  const panel=$('#folder-import-panel');if(!panel)return;
  const list=$('#folder-import-list'),title=$('#folder-import-title'),count=$('#folder-import-count');
  panel.classList.remove('is-error','is-empty','is-success');
  panel.classList.add(type==='error'?'is-error':type==='empty'?'is-empty':'is-success');
  title.textContent=folder;
  count.textContent=tracks&&tracks.length?(tracks.length===1?'1 música importada':tracks.length+' músicas importadas'):(message||'Aguardando músicas');
  list.innerHTML='';
  if(message){const row=document.createElement('div');row.className='folder-import-item import-message';row.innerHTML='<span class="folder-import-dot"></span><span class="folder-import-name"></span>';row.querySelector('.folder-import-name').textContent=message;list.appendChild(row);}
  (tracks||[]).slice(0,KND_MAX_IMPORT_FILES).forEach((t,i)=>{const row=document.createElement('div');row.className='folder-import-item';row.innerHTML='<span class="folder-import-index"></span><span class="folder-import-name"></span><span class="folder-import-meta"></span>';row.querySelector('.folder-import-index').textContent=String(i+1).padStart(2,'0');row.querySelector('.folder-import-name').textContent=t.title||t.folderPath||'Música';row.querySelector('.folder-import-meta').textContent=t.project||t.importFolder||'';list.appendChild(row);});
  panel.classList.add('show');
}

function showFolderImportPanel(folder,tracks){
  kndSetImportPanelState('success','Importação pronta: '+folder,tracks,'Limite por importação: até '+KND_MAX_IMPORT_FILES+' músicas.');
  const panel=$('#folder-import-panel');if(panel)panel.scrollIntoView({behavior:'smooth',block:'nearest'});
}
function showFolderImportError(message){
  kndSetImportPanelState('error','Nenhuma música importada',[],message);
}
async function importFolderFiles(fileList,{autoplay=false}={}){
  const incoming=Array.from(fileList||[]);
  const audio=incoming.filter(isAudioFile).sort((a,b)=>(a.webkitRelativePath||a.name).localeCompare(b.webkitRelativePath||b.name,undefined,{numeric:true,sensitivity:'base'}));
  const lrcMap=new Map(incoming.filter(f=>/\.lrc$/i.test(f.name)).map(f=>[cleanName(f.name).toLowerCase(),f]));
  if(!audio.length){showFolderImportError('Não encontrei arquivos de áudio compatíveis. Use MP3, WAV, M4A, FLAC, AAC, OGG ou OPUS.');toast('Nenhum áudio encontrado','e');return;}
  if(audio.length>KND_MAX_IMPORT_FILES){
    const preview=audio.slice(0,KND_MAX_IMPORT_FILES).map(f=>({title:cleanName(f.name),project:'Selecionada'}));
    kndSetImportPanelState('error','Limite de importação atingido',preview,'Você selecionou '+audio.length+' músicas. Importe no máximo '+KND_MAX_IMPORT_FILES+' por vez para evitar travamentos no celular.');
    toast('Limite de '+KND_MAX_IMPORT_FILES+' músicas por vez','e');return;
  }
  const files=audio;
  const folder=(files[0].webkitRelativePath?files[0].webkitRelativePath.split('/')[0]:(files.length>1?'Músicas selecionadas':'Música selecionada'))||'Músicas selecionadas';
  const btn=$('#btn-auto-play-folder'),btn2=$('#btn-open-folder'),oldText=btn?.textContent,oldText2=btn2?.textContent;
  if(btn){btn.textContent='Importando...';btn.disabled=true;} if(btn2){btn2.textContent='Importando...';btn2.disabled=true;}
  toast('Lendo pasta: '+files.length+' música(s)','i');
  try{
    const now=Date.now();let count=0;const imported=[];
    for(const file of files){
      const meta=await readLocalMetadata(file);const buf=await f2buf(file);
      const lrcFile=lrcMap.get(cleanName(file.name).toLowerCase());
      const lrcText=lrcFile?await readTextFile(lrcFile):'';
      const t={id:'t_'+Date.now()+'_'+Math.random().toString(36).slice(2),title:meta.title||cleanName(file.name),project:meta.project||folder,genre:meta.genre||'Outro',lyrics:lrcText,description:meta.album?('Álbum: '+meta.album):('Importado de '+folder),audioBuffer:buf,mimeType:file.type||'audio/mpeg',coverUrl:meta.coverUrl||'',createdAt:now+count,folderPath:file.webkitRelativePath||file.name,importFolder:folder,lrcLines:lrcText?parseLRC(lrcText):[],mood:estimateTrackMood({title:meta.title||file.name,project:meta.project||folder,genre:meta.genre||'Outro',description:meta.album||''})};
      await dbPut(t);imported.push(t);count++;
    }
    await loadTracks();S.context=folder;S.libFilter='all';S.libSearch='';renderLibrary();renderQueue();showFolderImportPanel(folder,imported);toast(count+' música(s) adicionada(s) à biblioteca com fila inteligente','s');
    if(autoplay){S.repeatMode='all';S.smartAutoplay=true;$('#repeat-btn')?.classList.add('on');const firstId=imported[0]?.id;const firstIndex=S.tracks.findIndex(t=>t.id===firstId);await playTrack(firstIndex>=0?firstIndex:0,folder);}
    else{showPage('library');}
  }catch(e){console.error(e);showFolderImportError(e.name==='QuotaExceededError'?'O armazenamento local do navegador está cheio.':'Não consegui finalizar a importação. Tente uma pasta menor ou outro navegador.');toast(e.name==='QuotaExceededError'?'Armazenamento cheio':'Erro ao importar pasta','e');}
  finally{if(btn){btn.textContent=oldText;btn.disabled=false;} if(btn2){btn2.textContent=oldText2;btn2.disabled=false;}}
}

/* ── UPLOAD ───────────────────────────────────────────────── */
function bindUpload(){
  const drop=$('#upload-drop'),fi=$('#track-file'),folderFi=$('#folder-file');
  ['dragover','dragenter'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.add('drag');}));
  ['dragleave','drop'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.remove('drag');}));
  drop.addEventListener('drop',ev=>{const files=Array.from(ev.dataTransfer.files||[]).filter(isAudioFile);if(files.length){importFolderFiles(files,{autoplay:true});}});
  fi.addEventListener('change',()=>{const files=Array.from(fi.files||[]).filter(isAudioFile);if(!files.length)return;importFolderFiles(files,{autoplay:false});fi.value='';});
  $('#btn-open-folder')?.addEventListener('click',e=>{e.preventDefault();folderFi.dataset.autoplay='0';folderFi.click();});
  $('#btn-auto-play-folder')?.addEventListener('click',e=>{e.preventDefault();folderFi.dataset.autoplay='1';folderFi.click();});
  folderFi?.addEventListener('change',()=>{if(folderFi.files?.length)importFolderFiles(folderFi.files,{autoplay:folderFi.dataset.autoplay==='1'});folderFi.value='';});
  $('#folder-go-library')?.addEventListener('click',e=>{e.preventDefault();showPage('library');});
  $('#folder-play-now')?.addEventListener('click',async e=>{e.preventDefault();if(!S.tracks.length){toast('Importe músicas primeiro','e');return;}S.repeatMode='all';S.smartAutoplay=true;$('#repeat-btn')?.classList.add('on');const ctx=S.context||'Biblioteca';const first=S.tracks.findIndex(t=>folderLabel(t)===ctx);await playTrack(first>=0?first:(S.currentIdx>=0?S.currentIdx:0),ctx);});
  function onFile(f){$('#file-preview').classList.add('show');$('#fp-name').textContent=f.name;$('#fp-size').textContent=fmtSz(f.size);if(!$('#track-title').value)$('#track-title').value=f.name.replace(/\.[^.]+$/,'').replace(/[-_]/g,' ');}
  $('#btn-save').addEventListener('click',saveTrack);
  $('#btn-clear').addEventListener('click',clearUpload);
}
async function saveTrack(){
  const af=$('#track-file').files[0],cf=$('#cover-file').files[0],ti=$('#track-title').value.trim();
  if(!af||!ti){toast('Adicione o arquivo e o título','e');return;}
  const btn=$('#btn-save');btn.textContent='Salvando...';btn.disabled=true;
  try{
    const[buf,cov]=await Promise.all([f2buf(af),f2url(cf)]);
    const t={id:'t_'+Date.now()+'_'+Math.random().toString(36).slice(2),title:ti,project:$('#track-project').value.trim(),genre:$('#track-genre').value,lyrics:$('#track-lyrics').value.trim(),description:$('#track-desc').value.trim(),audioBuffer:buf,mimeType:af.type||'audio/mpeg',coverUrl:cov||'',createdAt:Date.now()};
    await dbPut(t);await loadTracks();clearUpload();showPage('library');toast('Música salva ✓');
  }catch(e){if(e.name==='QuotaExceededError')toast('Armazenamento cheio','e');else toast('Erro: '+e.message,'e');}
  finally{btn.textContent='Salvar localmente';btn.disabled=false;}
}
function clearUpload(){['track-file','cover-file','track-title','track-project','track-lyrics','track-desc'].forEach(id=>{const el=$('#'+id);if(el)el.value='';});$('#track-genre').value='Eletrônico';$('#file-preview').classList.remove('show');}

/* ── LOAD TRACKS ──────────────────────────────────────────── */
async function loadTracks(){
  const raw=await dbAll();raw.sort((a,b)=>b.createdAt-a.createdAt);
  S.tracks.forEach(t=>{if(t._url?.startsWith('blob:'))URL.revokeObjectURL(t._url);});
  S.tracks=raw.map(t=>{t._url=mkURL(t);return t;});
  renderFeatured();renderRecents();renderContinue();renderLibrary();renderLibTabs();updateHero();
  if(S.currentIdx===-1&&S.tracks.length)S.currentIdx=0;
}

/* ── ZOOM PREVENTION ─────────────────────────────────────── */
// Block pinch-zoom and double-tap zoom for app-like feel.
['gesturestart','gesturechange','gestureend'].forEach(ev=>{
  document.addEventListener(ev,e=>e.preventDefault(),{passive:false});
});
let _lastTouchEnd=0;
document.addEventListener('touchend',e=>{
  const now=Date.now();
  if(now-_lastTouchEnd<320) e.preventDefault();
  _lastTouchEnd=now;
},{passive:false});
document.addEventListener('touchmove',e=>{
  if(e.scale&&e.scale!==1) e.preventDefault();
},{passive:false});
document.addEventListener('wheel',e=>{
  if(e.ctrlKey) e.preventDefault();
},{passive:false});
document.addEventListener('keydown',e=>{
  if((e.ctrlKey||e.metaKey)&&['+','-','=','0'].includes(e.key)) e.preventDefault();
});

/* ── THEME (light / dark / auto) ─────────────────────────── */
function getSystemTheme(){
  return window.matchMedia&&window.matchMedia('(prefers-color-scheme: light)').matches?'light':'dark';
}
function resolveTheme(pref){
  return pref==='auto'?getSystemTheme():pref;
}
function applyTheme(pref){
  const theme=resolveTheme(pref);
  document.documentElement.setAttribute('data-theme',theme);
  const meta=document.querySelector('meta[name="theme-color"]');
  if(meta) meta.setAttribute('content',theme==='light'?'#f3f5f9':'#040608');
  $$('[data-theme-opt]').forEach(b=>b.classList.toggle('on',b.dataset.themeOpt===pref));
}
function setThemePreference(pref){
  S.themePref=pref;
  localStorage.setItem('knd_theme',pref);
  applyTheme(pref);
}
if(window.matchMedia){
  window.matchMedia('(prefers-color-scheme: light)').addEventListener('change',()=>{
    if(S.themePref==='auto') applyTheme('auto');
  });
}

/* ── USER NAME / PROFILE ─────────────────────────────────── */
function applyUserName(){
  const name=S.userName||'Dion Kennedy';
  const ini=getInitials(name);
  // Update all avatar buttons
  $$('#user-avatar, #lib-avatar').forEach(el=>el.textContent=ini);
  // Update settings row
  const userRow=$('#s-user-name');if(userRow)userRow.textContent=name;
  const userRowSub=$('#s-user-sub');if(userRowSub)userRowSub.textContent='KND Apps · Conta local';
}
function openProfileModal(){
  $('#profile-name-input').value=S.userName||'';
  $('#profile-overlay').classList.add('on');
  $('#profile-modal').classList.add('on');
  setTimeout(()=>$('#profile-name-input').focus(),200);
}
function closeProfileModal(){
  $('#profile-overlay').classList.remove('on');
  $('#profile-modal').classList.remove('on');
}
function saveProfile(){
  const name=$('#profile-name-input').value.trim();
  if(!name){toast('Digite seu nome','e');return;}
  S.userName=name;
  localStorage.setItem('knd_user_name',name);
  applyUserName();
  closeProfileModal();
  toast(`Bem-vindo, ${name.split(' ')[0]} ✓`,'s');
}
function maybeShowFirstSetup(){
  if(!localStorage.getItem('knd_user_name')){
    setTimeout(()=>openProfileModal(),900);
  }
}
/* ── FULLSCREEN HELPER ───────────────────────────────────── */
function tryEnterFullscreen(){
  const el=document.documentElement;
  const req=el.requestFullscreen||el.webkitRequestFullscreen||el.mozRequestFullScreen;
  if(req&&!document.fullscreenElement){
    req.call(el,{navigationUI:'hide'}).catch(()=>{});
  }
}


const CAST={supported:false,connected:false,searching:false,deviceName:'',mode:'',lastError:''};
function ensureCastPill(){
  let pill=$('#player-cast-pill');
  if(pill)return pill;
  const host=$('.player-info-text')||$('.player-info');
  if(!host)return null;
  pill=document.createElement('div');
  pill.id='player-cast-pill';
  pill.className='player-cast-pill';
  pill.innerHTML='<span class="cast-dot"></span><span id="player-cast-label">Cast pronto</span>';
  host.appendChild(pill);
  return pill;
}
function setCastUI(state,msg,type='i'){
  const btn=$('#pe-cast');
  const pill=ensureCastPill();
  if(btn){
    btn.classList.toggle('searching',state==='searching');
    btn.classList.toggle('casting',state==='connected');
    btn.classList.toggle('on',state==='available'||state==='connected');
    btn.setAttribute('aria-pressed',state==='connected'?'true':'false');
  }
  if(pill){
    pill.classList.toggle('show',state==='connected'||state==='searching');
    pill.classList.toggle('connected',state==='connected');
    pill.classList.toggle('searching',state==='searching');
    const label=pill.querySelector('#player-cast-label');
    if(label)label.textContent=msg||'Cast pronto';
  }
  if(msg)announceCastStatus(msg,type);
}
async function startCastPlayback(){
  const audio=$('#audio');
  if(!audio)return;
  if(!audio.src&&S.currentIdx>=0&&S.tracks[S.currentIdx])audio.src=S.tracks[S.currentIdx]._url;
  if(!audio.src&&S.tracks.length){await playTrack(S.currentIdx>=0?S.currentIdx:0,S.context||'Biblioteca');return;}
  try{initAudio();await resumeCtx();await audio.play();setPlayState(true);startVis();}
  catch(e){toast('Toque em play se a TV não iniciar automaticamente','i');}
}
function castDeviceLabel(mode='TV'){
  return mode==='AirPlay'?'AirPlay conectado':'TV conectada';
}
function isLocalBlobAudio(){
  const audio=$('#audio');
  return !!(audio&&audio.src&&audio.src.startsWith('blob:'));
}
function explainCastFailure(err){
  const name=(err&&err.name)||'';
  if(name==='AbortError')return 'Nenhuma TV foi escolhida. Toque no ícone e selecione o dispositivo na janela do navegador.';
  if(name==='NotAllowedError')return 'O navegador bloqueou a transmissão. Toque novamente no botão Cast e permita a conexão.';
  if(name==='NotFoundError')return 'Nenhum dispositivo compatível encontrado nesta rede Wi-Fi.';
  if(name==='NotSupportedError')return 'Este navegador não consegue transmitir este áudio local diretamente. Use o modo Transmitir tela/guia.';
  return 'Não consegui conectar via Cast nativo. Tente Transmitir tela/guia pelo navegador.';
}
function showCastHelp(message){
  const local=isLocalBlobAudio();
  const extra=local?' Arquivos locais de pasta podem não ser aceitos pelo Chromecast via Remote Playback, porque a TV não consegue acessar o arquivo local do celular. Nesse caso, use Transmitir tela/guia.':'';
  setCastUI('available',message+extra,'i');
}
async function prepareAudioForCast(){
  const audio=$('#audio');
  if(!audio)return false;
  if(!audio.src&&S.currentIdx>=0&&S.tracks[S.currentIdx])audio.src=S.tracks[S.currentIdx]._url;
  if(!audio.src&&S.tracks.length){
    await playTrack(S.currentIdx>=0?S.currentIdx:0,S.context||'Biblioteca');
  }
  try{audio.load?.();}catch(e){}
  return !!audio.src;
}
async function openNativeCast(){
  const audio=$('#audio');
  if(!audio){toast('Player não encontrado','e');return;}
  if(!S.tracks.length&&!audio.src){toast('Adicione uma música antes de transmitir','e');return;}
  const ready=await prepareAudioForCast();
  if(!ready){toast('Carregue uma música antes de transmitir','e');return;}
  setCastUI('searching','Procurando TV compatível...','i');
  try{
    if(audio.webkitShowPlaybackTargetPicker){
      CAST.mode='AirPlay';
      audio.webkitShowPlaybackTargetPicker();
      announceCastStatus('Escolha a TV/AirPlay na janela do sistema.','i');
      setTimeout(()=>{if(!CAST.connected)setCastUI('available','Nenhum AirPlay conectado. Toque no ícone para tentar de novo.','i');},12000);
      return;
    }
    if(audio.remote&&typeof audio.remote.prompt==='function'){
      CAST.mode='Remote Playback';
      await audio.remote.prompt();
      await startCastPlayback();
      CAST.connected=true;
      CAST.deviceName=castDeviceLabel('TV');
      setCastUI('connected',CAST.deviceName,'s');
      return;
    }
    showCastHelp('Cast nativo indisponível neste navegador.');
  }catch(err){
    CAST.connected=false;
    CAST.lastError=(err&&err.name)||'unknown';
    showCastHelp(explainCastFailure(err));
  }
}
function setupNativeCast(){
  const audio=$('#audio'),btn=$('#pe-cast');
  if(!audio||!btn)return;
  audio.disableRemotePlayback=false;
  ensureCastPill();
  const supported=!!(audio.remote&&typeof audio.remote.prompt==='function')||!!audio.webkitShowPlaybackTargetPicker;
  CAST.supported=supported;
  btn.style.opacity=supported?'1':'.5';
  btn.title=supported?'Transmitir para TV':'Cast nativo indisponível neste navegador';
  const st=$('#cast-status');if(st)st.textContent=supported?'Cast pronto: toque no ícone da TV. Se a busca fechar, use Transmitir tela/guia no navegador.':'Cast indisponível neste navegador';
  if(audio.remote){
    audio.remote.watchAvailability?.(available=>{if(!CAST.connected){btn.classList.toggle('on',!!available);btn.style.opacity=available?'1':'.65';}}).catch(()=>{});
    audio.remote.addEventListener?.('connecting',()=>setCastUI('searching','Conectando à TV...','i'));
    audio.remote.addEventListener?.('connect',async()=>{CAST.connected=true;CAST.deviceName=castDeviceLabel('TV');await startCastPlayback();setCastUI('connected',CAST.deviceName,'s');});
    audio.remote.addEventListener?.('disconnect',()=>{CAST.connected=false;CAST.deviceName='';setCastUI('available','Cast desconectado','i');});
  }
  audio.addEventListener('webkitcurrentplaybacktargetiswirelesschanged',async()=>{
    if(audio.webkitCurrentPlaybackTargetIsWireless){
      CAST.connected=true;CAST.mode='AirPlay';CAST.deviceName=castDeviceLabel('AirPlay');
      await startCastPlayback();
      setCastUI('connected',CAST.deviceName,'s');
    }else{
      CAST.connected=false;CAST.deviceName='';setCastUI('available','AirPlay desconectado','i');
    }
  });
}

/* ── BIND ALL ─────────────────────────────────────────────── */
function bindUI(){
  // Login
  $('#btn-enter').addEventListener('click',()=>{
    tryEnterFullscreen();
    $('#screen-login').style.display='none';
    $('#screen-app').style.display='block';
    showPage('home');
    maybeShowFirstSetup();
  });

  // Nav
  $$('.nav-tab').forEach(t=>t.addEventListener('click',()=>showPage(t.dataset.tab)));

  // Global search → opens search page
  $('#g-search-input').addEventListener('click',()=>{showPage('search');setTimeout(()=>$('#page-search-input').focus(),200);});

  // Home chips
  $$('[data-home]').forEach(btn=>btn.addEventListener('click',()=>{
    S.homeFilter=btn.dataset.home;$$('[data-home]').forEach(b=>b.classList.remove('on'));btn.classList.add('on');
    const hero=$('#parallax-hero'),heads=$$('#page-home .sh'),feat=$('#featured-cards'),rw=$('#home-recents-wrap');
    if(S.homeFilter==='all'){[hero,...heads,feat,rw].forEach(el=>{if(el)el.style.display='';});renderRecents();renderFeatured();renderContinue();}
    else{[hero,...heads.slice(0,1),feat,rw].forEach(el=>{if(el)el.style.display='none';});renderHomeFavs();}
  }));

  // Hero play
  $('#ph-play').addEventListener('click',()=>S.tracks.length?playTrack(0,'Biblioteca'):showPage('upload'));
  $('#link-all').addEventListener('click',()=>showPage('library'));

  // Library
  $('#btn-upload-lib').addEventListener('click',()=>showPage('upload'));
  $('#lib-avatar').addEventListener('click',()=>showPage('settings'));
  $('#btn-lib-search-tog').addEventListener('click',()=>{const b=$('#lib-search-bar');b.classList.toggle('hidden');if(!b.classList.contains('hidden'))$('#lib-search-input').focus();else{S.libSearch='';renderLibrary();}});
  $('#btn-lib-search-close').addEventListener('click',()=>{$('#lib-search-bar').classList.add('hidden');S.libSearch='';renderLibrary();});
  $('#lib-search-input').addEventListener('input',e=>{S.libSearch=e.target.value;renderLibrary();});
  $$('[data-lf]').forEach(btn=>btn.addEventListener('click',()=>{S.libFilter=btn.dataset.lf;$$('.filter-tab').forEach(t=>t.classList.remove('on'));btn.classList.add('on');renderLibrary();}));
  $('#btn-lib-sort').addEventListener('click',()=>{S.libSort=S.libSort==='recent'?'az':'recent';$('#lib-sort-label').textContent=S.libSort==='recent'?'Recentes':'A–Z';renderLibrary();});

  // Search
  $('#page-search-input').addEventListener('input',e=>renderSearch(e.target.value));

  // Mini player
  $('#mini-bar').addEventListener('click',()=>showPage('player'));
  $('#mini-play').addEventListener('click',e=>{e.stopPropagation();togglePlay();});
  $('#mini-prev').addEventListener('click',e=>{e.stopPropagation();prevTrack();});
  $('#mini-next').addEventListener('click',e=>{e.stopPropagation();nextTrack();});

  // Player controls
  $('#btn-player-back').addEventListener('click',()=>showPage(prevPage));
  $('#btn-player-opts').addEventListener('click',()=>{if(S.currentIdx>=0)openSheet(S.currentIdx);});
  $('#btn-play').addEventListener('click',togglePlay);
  $('#btn-prev').addEventListener('click',prevTrack);
  $('#btn-next').addEventListener('click',nextTrack);
  $('#player-fav').addEventListener('click',()=>{const t=S.tracks[S.currentIdx];if(t)toggleFav(t.id);});
  $('#shuffle-btn').addEventListener('click',()=>{S.shuffle=!S.shuffle;$('#shuffle-btn').classList.toggle('on',S.shuffle);toast(S.shuffle?'Modo aleatório ativo':'Aleatório desativado');});
  $('#repeat-btn').addEventListener('click',()=>{S.repeatMode=S.repeatMode==='off'?'all':(S.repeatMode==='all'?'one':'off');$('#repeat-btn').classList.toggle('on',S.repeatMode!=='off');const m={off:'Repetir',all:'Repetir tudo',one:'Repetir 1'};if($('#qf-rpt-label'))$('#qf-rpt-label').textContent=m[S.repeatMode];});
  $('#pe-remaster').addEventListener('click',()=>{S.remaster=!S.remaster;$('#pe-remaster').classList.toggle('on',S.remaster);initAudio();if(actx&&nAir){nAir.gain.value=parseFloat($('#eq-air').value)+(S.remaster?3.5:0);nPresence.gain.value=parseFloat($('#eq-presence').value)+(S.remaster?2.5:0);}toast(S.remaster?'⭐ Remaster HD ativo':'Remaster desativado',S.remaster?'g':'i');});
  $('#pe-eq').addEventListener('click',()=>showPage('settings'));
  $('#pe-cast').addEventListener('click',openNativeCast);
  $('#pe-queue').addEventListener('click',openQueue);
  $('#spatial-badge-btn').addEventListener('click',()=>{const modes=['flat','spatial','hifi','bass','vocal','cinema'];const cur=modes.indexOf(S.spatialMode);const next=modes[(cur+1)%modes.length];applyPreset(next);if(actx)applyEQToNodes();toast(`🎧 ${PRESETS[next].label} ativado`,'g');});

  // Avatar → settings
  $('#user-avatar').addEventListener('click',()=>showPage('settings'));

  // Sheet
  $('#sheet-overlay').addEventListener('click',closeSheet);
  $('#sh-play').addEventListener('click',()=>{const i=shIdx;closeSheet();playTrack(i);});
  $('#sh-next').addEventListener('click',()=>{const i=shIdx;closeSheet();S.upNext.unshift(i);toast('Tocará a seguir: '+S.tracks[i]?.title,'i');});
  $('#sh-queue').addEventListener('click',()=>{const i=shIdx;closeSheet();S.upNext.push(i);toast('Adicionada à fila','i');});
  $('#sh-fav').addEventListener('click',()=>{const t=S.tracks[shIdx];if(!t)return;toggleFav(t.id);$('#sh-fav').classList.toggle('fav-on',isFav(t.id));$('#sh-fav-label').textContent=isFav(t.id)?'Remover dos favoritos':'Favoritar';});
  $('#sh-edit').addEventListener('click',()=>openEdit(shIdx));
  $('#sh-delete').addEventListener('click',()=>deleteTrack(shIdx));

  // Edit
  $('#modal-overlay').addEventListener('click',closeEdit);
  $('#modal-cancel').addEventListener('click',closeEdit);
  $('#modal-save').addEventListener('click',saveEdit);

  // Queue
  $('#queue-overlay').addEventListener('click',closeQueue);
  $('#qf-shuffle').addEventListener('click',()=>{S.shuffle=!S.shuffle;$('#shuffle-btn').classList.toggle('on',S.shuffle);$('#qf-shuffle').classList.toggle('on-g',S.shuffle);});
  $('#qf-repeat').addEventListener('click',()=>{S.repeatMode=S.repeatMode==='off'?'all':(S.repeatMode==='all'?'one':'off');const m={off:'Repetir',all:'Repetir tudo',one:'Repetir 1'};$('#qf-rpt-label').textContent=m[S.repeatMode];$('#qf-repeat').classList.toggle('on',S.repeatMode!=='off');$('#repeat-btn').classList.toggle('on',S.repeatMode!=='off');});

  // Settings - EQ
  ['eq-sub','eq-bass','eq-lmid','eq-mid','eq-hmid','eq-presence','eq-air','eq-exciter','eq-width','eq-reverb'].forEach(id=>{const el=$('#'+id);if(el)el.addEventListener('input',()=>{if(actx)applyEQToNodes();syncEQLabels();});});
  $$('[data-preset]').forEach(b=>b.addEventListener('click',()=>applyPreset(b.dataset.preset)));

  // Clear all
  $('#btn-clear-all').addEventListener('click',async()=>{const ok=await showConfirm('Limpar biblioteca','Excluir TODAS as músicas permanentemente?');if(!ok)return;S.tracks.forEach(t=>{if(t._url?.startsWith('blob:'))URL.revokeObjectURL(t._url);});await dbClear();$('#audio').pause();$('#audio').src='';S.currentIdx=-1;setPlayState(false);stopVis();$('#mini-bar').style.display='none';S.favorites=[];saveFavs();await loadTracks();toast('Biblioteca limpa');});

  // Theme buttons
  $$('[data-theme-opt]').forEach(b=>b.addEventListener('click',()=>setThemePreference(b.dataset.themeOpt)));

  // Profile modal
  $('#btn-edit-profile').addEventListener('click',openProfileModal);
  $('#profile-overlay').addEventListener('click',closeProfileModal);
  $('#profile-cancel').addEventListener('click',closeProfileModal);
  $('#profile-save').addEventListener('click',saveProfile);
  $('#profile-name-input').addEventListener('input',e=>{
    const ini=getInitials(e.target.value||'KW');
    const av=$('#profile-preview-avatar');if(av)av.textContent=ini;
  });
  $('#profile-name-input').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();saveProfile();}});

  // Audio events
  const audio=$('#audio');
  audio.addEventListener('play',async()=>{initAudio();await resumeCtx();applySmartVolume();setPlayState(true);});
  audio.addEventListener('pause',()=>setPlayState(false));
  audio.addEventListener('timeupdate',()=>{if(scrubbing)return;const pct=audio.duration?(audio.currentTime/audio.duration)*100:0;$('#prog-fill').style.width=pct+'%';$('#mini-prog-fill').style.width=pct+'%';$('#t-cur').textContent=fmtT(audio.currentTime);$('#t-total').textContent=fmtT(audio.duration);if(audio.duration&&audio.duration-audio.currentTime<18)preloadNextTrack();if(Math.floor(audio.currentTime)%10===0)saveLastSession();});
  audio.addEventListener('ended',async()=>{if(S.repeatMode==='one'){audio.currentTime=0;await audio.play();return;}if(S.smartAutoplay||S.repeatMode==='all'||S.upNext.length)await nextTrack();else setPlayState(false);});
  audio.addEventListener('error',()=>toast('Erro ao carregar áudio','e'));

  // Announcer skip
  $('#announcer-skip').addEventListener('click',()=>{speechSynthesis.cancel();$('#announcer-overlay').classList.remove('show');announcerBusy=false;if($('#audio').paused&&S.currentIdx>=0)$('#audio').play().catch(()=>{});});

  // Resize
  window.addEventListener('resize',resizeCvs);

  bindProgress();
  bindUpload();
}

/* ── SERVICE WORKER ───────────────────────────────────────── */
if('serviceWorker' in navigator)navigator.serviceWorker.register('./sw.js').catch(()=>{});

/* ── INIT ─────────────────────────────────────────────────── */
window.addEventListener('DOMContentLoaded',async()=>{
  applyTheme(S.themePref);
  setupNativeCast();
  setTimeout(()=>$('#splash-fill').style.width='100%',80);
  bindUI();syncEQLabels();applyPreset('spatial');
  await openDB();
  try{const d=JSON.parse(localStorage.getItem('knd_usage')||'{}');S.playCount=d.p||{};S.history=d.h||[];}catch(e){}
  await loadTracks();
  initCanvas();
  applyUserName();
  // Pre-load voices for speech synthesis
  if('speechSynthesis' in window){speechSynthesis.getVoices();speechSynthesis.addEventListener('voiceschanged',()=>{},{ once:true });}
  setTimeout(()=>$('#splash').classList.add('hide'),3000);
});

/* KND PWA INSTALL UX */
let kndInstallPromptEvent=null;
function kndIsStandalone(){return window.matchMedia('(display-mode: standalone)').matches||window.navigator.standalone===true;}
function kndCreateInstallPill(){
  if(document.getElementById('knd-install-pill')||kndIsStandalone())return;
  const pill=document.createElement('div');
  pill.id='knd-install-pill';
  pill.className='knd-install-pill';
  pill.innerHTML='<div class="knd-install-icon">⌁</div><div class="knd-install-copy"><strong>Instalar KND WAVES</strong><span>Use como app, com biblioteca offline e tela cheia.</span></div><div class="knd-install-actions"><button class="knd-install-primary" id="knd-install-now" type="button">Instalar</button><button class="knd-install-close" id="knd-install-close" type="button" aria-label="Fechar">×</button></div>';
  document.body.appendChild(pill);
  document.getElementById('knd-install-close')?.addEventListener('click',()=>{pill.classList.remove('show');localStorage.setItem('knd_install_dismissed',String(Date.now()));});
  document.getElementById('knd-install-now')?.addEventListener('click',async()=>{
    if(!kndInstallPromptEvent){toast('Abra o menu do navegador e toque em “Adicionar à tela inicial”.','i');return;}
    kndInstallPromptEvent.prompt();
    const choice=await kndInstallPromptEvent.userChoice.catch(()=>null);
    kndInstallPromptEvent=null;
    pill.classList.remove('show');
    if(choice?.outcome==='accepted')toast('KND WAVES instalado.','s');
  });
}
function kndMaybeShowInstallPill(){
  if(kndIsStandalone())return;
  const dismissed=Number(localStorage.getItem('knd_install_dismissed')||0);
  if(Date.now()-dismissed<86400000)return;
  kndCreateInstallPill();
  setTimeout(()=>document.getElementById('knd-install-pill')?.classList.add('show'),900);
}
window.addEventListener('beforeinstallprompt',(e)=>{e.preventDefault();kndInstallPromptEvent=e;kndMaybeShowInstallPill();});
window.addEventListener('appinstalled',()=>{document.getElementById('knd-install-pill')?.classList.remove('show');toast('KND WAVES instalado com sucesso.','s');});
window.addEventListener('DOMContentLoaded',()=>setTimeout(kndMaybeShowInstallPill,4200));

// KND final UX helpers
setTimeout(()=>{
  const card=document.getElementById('manual-upload-card');
  const toggle=document.getElementById('manual-upload-toggle');
  if(card&&toggle&&!toggle.dataset.bound){
    toggle.dataset.bound='1';
    toggle.addEventListener('click',(e)=>{
      if(e.target&&e.target.closest('input,textarea,select'))return;
      card.classList.toggle('is-collapsed');
      const btn=card.querySelector('.manual-toggle-btn');
      if(btn)btn.textContent=card.classList.contains('is-collapsed')?'Abrir':'Fechar';
    });
  }
},500);
