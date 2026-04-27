const CACHE='knd-waves-corrigido-final-v3';
self.addEventListener('install',e=>{self.skipWaiting()});
self.addEventListener('activate',e=>{self.clients.claim()});
self.addEventListener('fetch',e=>{});
