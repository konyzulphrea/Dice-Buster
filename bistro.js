// Big Integer String Operations - bistro.js ver 0.86 20141021
// Copyright (C) 2012-2014 Alexei Kourbatov, JavaScripter.net
//
// Based in part on the public-domain BigInt.js library; see http://leemon.com/crypto/BigInt.html

// CONSTANTS:
bi_MAXINT = 9007199254740991
bi_RADIX  = 10000000
bi_RADINV = 1/bi_RADIX
bi_RADSQR = bi_RADIX*bi_RADIX
bi_LRADIX = 1000000000000000
bi_ONE    = [1,0]; 


function repeat(s,n) {var r=''; if (n>3000000) n=0; while(n>0) {if(n&1) r+=s; if(n>>=1) s+=s;} return r;}

function bi_trim0(s) {  // trim leading zeros from an "integer" string s
 while (s.charAt(0)=='0' && s.length>1) s=s.substring(1);
 return s;
}

function vld(s) {
 var i, s = s.toString().replace(/[^\-\d]/g,'');

 if (s.lastIndexOf('-')>0) s='-'+s.replace(/\-/g,'');
 if (!s.match(/[1-9]/)) s='0';
 else {
  if (s.charAt(0)=='0')    s=s.replace(/^0+/,'');
  if (s.substr(0,2)=='-0') s=s.replace(/^\-0+/,'-');
 }
 return s;
}

function sgn(v) { // sign of v
 if (v=='0')           return  0;
 if (v.charAt(0)=='-') return -1;
 return 1;
}

function abv(v) { // absolute value of v 
 if (v.charAt(0)=='-') return v.substring(1);
 return v;
}

function bi_exp10(x1,x2) { 
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1), L1=a1.length;
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2), n2=parseInt(a2,10);

 if (s1== 1 && s2==-1) return (L1<=a2?'0':    a1.substring(0,L1-a2));
 if (s1==-1 && s2==-1) return (L1<=a2?'0':'-'+a1.substring(0,L1-a2));

 if (s1!= 0 && s2==1)  return v1+repeat('0',n2);
 if (s1!= 0 && s2==0)  return v1;

 return '0';
}


// function less(v1,v2) returns true iff v1 < v2 (numerically)
// works with pre-validated "signed integer" strings v1, v2
function less(v1,v2) { 
 var s1=1; if (v1=='0') s1=0; if (v1.charAt(0)=='-') s1=-1;
 var s2=1; if (v2=='0') s2=0; if (v2.charAt(0)=='-') s2=-1;
 
 //if (v1==v2) return false;      // equal values
 if (s1!=s2) return (s1 < s2);  // different signs
 if (s1== 1) return (v1.length < v2.length || (v1.length == v2.length && v1 < v2) ) // unequal positives
 if (s1==-1) return (v1.length > v2.length || (v1.length == v2.length && v1 > v2) ) // unequal negatives
 return false;
}


function bi_square(x) { //HAC Algorithm 14.16
 var t, uv, xi, b=[], r=[], L=x.length, M=Math.ceil(L/7);

 if (x.charAt(0)=='-') {x=abv(x); L--}
 if (L<9 && (t=x*x)<=bi_MAXINT) return t.toString();

 for (var i=0,k=L; k>0; i++,k-=7) b[i] = x.substring(k-7,k)-0;
 for (var i=2*M-1; i>=0; i--)     r[i] = 0;

 for (var i=0,k=0;i<M;i++) {
  xi = b[i];
  uv = r[k] + xi*xi;
  r[k] = uv % bi_RADIX;
  xi*= 2;
  for (var j=i+1;j<M;j++) {
   uv = r[i+j] + xi*b[j] + Math.floor(bi_RADINV*uv);
   r[i+j] = uv % bi_RADIX;
  }
  r[i+M] = Math.floor(bi_RADINV*uv);
  k+=2;
 }
 for (var i=0;i<r.length;i++) {
  if (r[i]>=bi_RADIX) {r[i+1] += Math.floor(r[i]*bi_RADINV); r[i]=r[i]%bi_RADIX;}
  r[i] = (''+(bi_RADIX+r[i])).substring(1);
 }
 return bi_trim0(r.reverse().join(''));
}


function bi_squareV(b) {
 var uv, xi, r=[], M=b.length;
 for (var i=2*M-1; i>=0; i--) r[i] = 0;
 for (var i=0,k=0;i<M;i++) {
  xi = b[i];
  uv = r[k] + xi*xi;
  r[k] = uv % bi_RADIX;
  xi*= 2;
  for (var j=i+1;j<M;j++) {
   uv = r[i+j] + xi*b[j] + Math.floor(bi_RADINV*uv);
   r[i+j] = uv % bi_RADIX;
  }
  r[i+M] = Math.floor(bi_RADINV*uv);
  k+=2;
 }
 for (var i=0;i<r.length;i++) {
  if (r[i]>=bi_RADIX) {r[i+1] += Math.floor(r[i]*bi_RADINV); r[i]=r[i]%bi_RADIX;}
 }
 return r;
}


function bi_cube(x)   { return bi_multiply(x,bi_square(x)); }
function bi_pow(x1,x2){ 
 var r='1', v = vld(x1), v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2), len=v.length;
 var n = parseInt(a2,10), d=parseInt(a2.charAt(a2.length-1),10);

 if (s2 == 0 || v == '1' || v == '-1' && d % 2 == 0) return '1'
 if (v =='-1' && d%2 == 1) return '-1'
 if (s2 == -1 && v == '0') return 'Cannot divide by zero.'
 if (s2 == -1 || v == '0') return '0'

 if (a2.length > 6 || len==1 && n > 250000 || len>1 && n*v.length > 210000) return 'This computation would take too long.'

 while (n>0) {
  if (n & 1) r = bi_multiply(r,v);
  if (n>>=1) v = bi_square(v);
 }
 return r;
}

function bi_subtract(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);

 if (v1==v2) return '0';
 if (s2== 0) return v1; 
 if (s2 > 0) return bi_add(v1,'-'+a2);
 if (s2 < 0) return bi_add(v1,a2);
 return '0'
}


function bi_add(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);

 if (s1==0) return v2;
 if (s2==0) return v1;

 if (s1>=0 && s2>=0)    return     bi_addU(a1,a2); // two non-negatives
 if (s1<0  && s2<0)     return '-'+bi_addU(a1,a2); // two negatives
 if (s1==-s2 && a1==a2) return '0';               // equal and opposite
  
 if (s1<0) {                                      // unequal opposites
  if (less(a1,a2))  return     bi_subU(a2,a1);
  else              return '-'+bi_subU(a1,a2);
 }
 if (s2<0) {
  if (less(a2,a1))  return     bi_subU(a1,a2);
  else              return '-'+bi_subU(a2,a1);
 }
 return '0'
}


function bi_addU(a1,a2) {
 var L1=a1.length, L2=a2.length, L=Math.max(L1,L2), M=Math.ceil(L/15);
 var i=0, r=[]; r[M]=0;

 for (var k=0;k<L;k+=15) {
  r[i] = (a1.substring(L1-k-15,L1-k)-0) + (a2.substring(L2-k-15,L2-k)-0);
  i++;
 }
 for (var i=0;i<M;i++) {
  if (r[i] >= bi_LRADIX) r[i+1] += 1;
  r[i] = (''+(bi_LRADIX+r[i])).substring(1);
 }
 return bi_trim0(r.reverse().join(''));
}

function bi_subU(a1,a2) {  // expected: a1>a2
 var L1=a1.length, L2=a2.length, L=Math.max(L1,L2), M=Math.ceil(L/15);
 var i=0, r = new Array(M);

 for (var k=0;k<L;k+=15) {
  r[i] = a1.substring(L1-k-15,L1-k) - a2.substring(L2-k-15,L2-k);
  i++;
 }
 for (var i=0;i<M;i++) {
  if (r[i]<0) {r[i]+=bi_LRADIX; r[i+1]-=1;} // borrow
  r[i] = (''+(bi_LRADIX+r[i])).substring(1);
 }
 return bi_trim0(r.reverse().join(''));
}


function subtractUntilLess(a1,a2) {  // expected: a1>a2>0
 var L1=a1.length, L2=a2.length, L=Math.max(L1,L2), M=Math.ceil(L/15);
 var n, k, i=0, r=[], b1=[], b2=[]; r[M]=0;

 for (var i=0,k=0;k<L;k+=15,i++) {
  b1[i] = a1.substring(L1-k-15,L1-k)-0;
  b2[i] = a2.substring(L2-k-15,L2-k)-0;
 }
 while (!less_(b1,b2)) {
  for (var i=0;i<M;i++) {
   b1[i] = b1[i] - b2[i];
   if (b1[i]<0) {b1[i]+=bi_LRADIX; b1[i+1]-=1;} // borrow
  }
 }
 for (var i=0;i<M;i++) b1[i] = (''+(bi_LRADIX+b1[i])).substring(1);
 return bi_trim0(b1.reverse().join(''));
}


function less_(x,y) { // vectors x,y
 var i, xL = x.length, yL = y.length;
 if (xL < yL) {
  for (i=xL; i<yL; i++) if (y[i]) return 1;
  for (i=xL-1;i>=0;i--) {
   if (x[i] > y[i]) return 0;
   if (x[i] < y[i]) return 1;
  }
 }
 else {
  for (i=yL; i<xL; i++) if (x[i]) return 0;
  for (i=yL-1;i>=0;i--) {
   if (x[i] > y[i]) return 0;
   if (x[i] < y[i]) return 1;
  }
 }
 return 0;
}


function bi_halve(x) {
 var r, v=vld(x), k=parseInt(v,10);
 if (Math.abs(k)<=bi_MAXINT) {
  if (k>=0) return Math.floor(k/2).toString();
  else  return (-Math.floor(-k/2)).toString();
 }
 r = bi_multiplyInt(5,v);
 return r.substring(0,r.length-1);
}


// multiply integer n < 10^14  by "integer" string x

function bi_multiplyInt(n,a) { 
 var n = parseInt(n,10), m = Math.abs(n), sn = (n==0? 0:(m==n?1:-1)); 
 var sx=sgn(a); if(sx==-1) a=abv(a);
 var r=[], b, t, u, L=a.length, hi = Math.floor(m/bi_RADIX), lo = m % bi_RADIX;

 if (m==0 || a==0) return '0';
 if (m==1) {
  if (sn*sx == 1) return a;
  if (sn*sx ==-1) return '-'+a;
 }

 for (var i=1+Math.ceil(L/7); i>=0; i--) r[i]=0;

 if (hi==0) {
  for (var i=0,k=0; k<L; i++,k+=7) {
   t = m*a.substring(L-k-7,L-k);
   r[i] += t % bi_RADIX;
   r[i+1] += Math.floor(bi_RADINV*t);
  }
 }
 else {
  r[r.length] = 0;
  for (var i=0,k=0; k<L; i++,k+=7) {
   b = a.substring(L-k-7,L-k)-0;
   t = lo*b;
   u = hi*b;
   r[i] += t % bi_RADIX;
   r[i+1] += Math.floor(bi_RADINV*t) + u%bi_RADIX;
   r[i+2] += Math.floor(bi_RADINV*u);
  }
 }
 for (var i=0;i<r.length;i++) {
  if (r[i]>=bi_RADIX) {r[i+1] += Math.floor(bi_RADINV*r[i]); r[i]=r[i]%bi_RADIX;}
  r[i] = (''+(bi_RADIX+r[i])).substring(1);
 }
 if (sn*sx == 1) return     bi_trim0(r.reverse().join(''));
 if (sn*sx ==-1) return '-'+bi_trim0(r.reverse().join(''));
 return '0'
}


function bi_multiply(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);

 if (s1*s2 == 1) return     multiplyAbs(a1,a2);
 if (s1*s2 ==-1) return '-'+multiplyAbs(a1,a2);
 return '0'
}


function multiplyAbs(a1,a2) {
 if (a1==0 || a2==0) return '0';

 var L1=a1.length, M1=Math.ceil(L1/7);
 var L2=a2.length, M2=Math.ceil(L2/7);
 var t, b, b2=[], r=[]  //, b1=[];

 for (var i=0,k=L2; k>0; i++,k-=7)  b2[i] = a2.substring(k-7,k)-0;
 for (var i=M1+M2-1; i>=0; i--)     r[i]  = 0;

 for (var j=0,k=L1; k>0; j++,k-=7) {
  b = a1.substring(k-7,k)-0; 
  i = j+1;
  for (var l=0;l<M2;l++) {
   t = b*b2[l];
   r[j+l] += t % bi_RADIX;
   r[i+l] += Math.floor(bi_RADINV*t);
  }
 }

 for (var i=0;i<r.length;i++) {
  if (r[i]>=bi_RADIX) {r[i+1] += Math.floor(r[i]*bi_RADINV); r[i]=r[i]%bi_RADIX;}
  r[i] = (''+(bi_RADIX+r[i])).substring(1);
 }
 return bi_trim0(r.reverse().join(''));
}


function bi_divide(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);
 var r = '0';

 if (s1*s2==1 )  r =     divideAbs(a1,a2);
 if (s1*s2==-1)  r = '-'+divideAbs(a1,a2);

 if (s2==0)   return 'Cannot divide by zero.'
 if (r=='-0') return '0';
 return r;
}

function divideAbs(a1,a2) { 
 if (a2=='0')     return 'Cannot divide by zero.'
 if (a2=='1')     return a1;
 if (less(a1,a2)) return '0';
 if (a1==a2)      return '1';

 var x = bi_str2vec(a1,2);
 var y = bi_str2vec(a2,2);
 var q = new Array(x.length); // bi_copyInt_(q,0);
 var r = new Array(x.length); // bi_copyInt_(r,0);
 bi_divide_ (x,y,q,r);
 return bi_vec2str(q);
 function less(x,y) { return (x.length<y.length || x.length==y.length && x<y); }
}

function bi_mod(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);
 var r = '0';

 if (s2==0)   return 'x mod y  is the remainder r of the division x/y; it is undefined for y = 0. \nFor x,y > 0, the quotient q and remainder r are defined by  x = qy + r,  0 \u2264 r < y.\nFor any x and nonzero y, the remainder r satisfies:  x = qy + r,  |r| < |y|.';
 if (s1>0)    r =     bi_modU(a1,a2);
 if (s1<0)    r = '-'+bi_modU(a1,a2);
 if (r=='-0') return '0';
 return r;
}


function bi_factorial(x) {
 var e, j, k, m1, m2, r = '1', q = [];
 var v = vld(x), s = sgn(v), a = abv(v), n = parseInt(a, 10);
 
 if (s == -1) return 'Factorial x! is not defined for negative x.'
 if (v.length > 5 || n > 12000) return 'This computation would take too long.'
 if (s == 0) return '1'
 if (a == '1') return '1'
 if (a == '2') return '2'

 if (n < 1000) {
  if (n % 3 == 0)      { r='1'; for (k=2; k < n; k+=3) r = bi_multiplyInt((k-1)*k*(k+1), r); }
  else if (n%3 == 1) { r='1'; for (k=3; k < n; k+=3) r = bi_multiplyInt((k-1)*k*(k+1), r); }
  else if (n%3 == 2) { r='2'; for (k=4; k < n; k+=3) r = bi_multiplyInt((k-1)*k*(k+1), r); }
  return r;
 }

 for (j = 0; j < 16; j++) {
  q[j] = '1';
  e = Math.floor((j+1) * n/16);

  for (k = 1 + Math.floor(j*n/16); k <= e; k += 3) {
   m1 = k+1 > e ? 1 : k+1;
   m2 = k+2 > e ? 1 : k+2;
   q[j] = bi_multiplyInt(k*m1*m2, q[j]);
  }
 }

 for (j = 0; j < 16; j+=2) q[j] = multiplyAbs(q[j],q[j+1]);
 for (j = 0; j < 8;  j+=2) q[j] = multiplyAbs(q[j],q[14-j]);

 q[0] = multiplyAbs(q[0],q[6]);
 q[4] = multiplyAbs(q[4],q[2]);

 r = multiplyAbs(q[0],q[4]);
 return r;
}


function bi_primorial(x) {
 var j, k, L, m, e, q = [], r = '1';
 var v = vld(x), s = sgn(v), a = abv(v), n = parseInt(a, 10);

 if (s == -1) return 'Primorial x# is not defined for negative x.'
 if (v.length > 6 || n > 100002) return 'This computation would take too long.'
 if (s == 0) return '1'
 if (a == '1') return '1'
 if (a == '2') return '2'

 if (n <= 10000) {
  for (k = 1; primes[k] <= n; k+=2) r = bi_multiplyInt(primes[k-1] * primes[k], r);
  if (primes[k-1] <= n) r = bi_multiplyInt(primes[k-1], r);
  return r;
 }

 for (L = 1; primes[L] <= n; L++);

 for (j = 0; j < 16; j++) {
  q[j] = '1';
  e = Math.floor((j+1)*L/16) - 1;
  for (k = Math.floor(j*L/16) ; k <= e; k+=2) {
   m = ( k+1 > e ? 1 : primes[k+1] );
   q[j] = bi_multiplyInt(primes[k] * m, q[j]);
  }
 }
 for (j = 0; j < 16; j+=2) q[j] = multiplyAbs(q[j],q[j+1]);
 for (j = 0; j < 8;  j+=2) q[j] = multiplyAbs(q[j],q[14-j]);

 q[0] = multiplyAbs(q[0],q[6]);
 q[4] = multiplyAbs(q[4],q[2]);

 r = multiplyAbs(q[0], q[4]);
 return r;
}


//return array of all primes less than integer n
function bi_findPrimes(n) {
  var i,s,p,ans;
  s=new Array(n);
  for (i=1;i<n;i++) s[i]=0;
  s[0]=2;
  p=0;    //first p elements of s are primes, the rest are a sieve
  for(;s[p]<n;) {                           // s[p] is the pth prime
    for(i=s[p]*s[p]; i<n; i+=s[p]) s[i]=1;  // mark multiples of s[p]
    p++;
    s[p]=s[p-1]+1;
    for(; s[p]<n && s[s[p]]; s[p]++); //find next prime (where s[p]==0)
  }
  ans=new Array(p);
  for(i=0;i<p;i++)
    ans[i]=s[i];
  return ans;
}

primes = bi_findPrimes(100000);


function bi_odd(r)  { if (typeof r=='number') return(r%2==1); return ('13579'.indexOf(r.charAt(r.length-1)) != -1) }
function bi_even(r) { if (typeof r=='number') return(r%2==0); return ('02468'.indexOf(r.charAt(r.length-1)) != -1) }

function divisibleBy3or5or7or11or13(r) {
 var s, s0=0, s1=0, s2=0, s3=0, s4=0, s5=0, len=r.length, d=r.charAt(len-1);
 if (d==5 || d==0) return 1;

 for (var k=len-1; k>=0; k-=6) {
  s0 -= r.charAt(k)  ; s1 -= r.charAt(k-1); s2 -= r.charAt(k-2);
  s3 -= r.charAt(k-3); s4 -= r.charAt(k-4); s5 -= r.charAt(k-5);
 }
 if ((s0+s1+s2+s3+s4+s5) % 3==0)   return 1;
 s = s3-s0+10*(s4-s1)+100*(s5-s2);
 if (s%7==0 || s%11==0 || s%13==0) return 1;
 return 0;
}

// GCD-related code - based in part on HAC ch14 and BigInt.js 

function bi_LCM(x1,x2) {
 var v1 = vld(x1), s1 = sgn(v1), a1 = abv(v1);
 var v2 = vld(x2), s2 = sgn(v2), a2 = abv(v2);

 if (s1*s2==0) return 'LCM(x,y) is the least common multiple of x and y. \nLCM(x,y) is not defined for zero input.'

 var gcd = bi_GCD(a1,a2);
 if (gcd=='1') return multiplyAbs(a1,a2);

 return divideAbs (multiplyAbs(a1,a2), gcd);
}

function bi_linComb_(x,y,a,b) {  // assuming x >= y >= 0, let x = ax+by
  var i, c=0, xL=x.length, yL=y.length, k=Math.min(xL, yL);

  for (i=0;i<k;i++) {
    c  += a*x[i] + b*y[i];
    x[i]= c % bi_RADIX;
    c   = Math.floor(c*bi_RADINV);
  }
  for (i=k;i<xL;i++) {
    c  += a*x[i];
    x[i]= c % bi_RADIX;
    c   = Math.floor(c*bi_RADINV);
  }
}

// bi_str2vec creates and returns a new vector with elements determined by s
// if len is not supplied, the vector's length will be as needed to fit s, plus one high-order zero element

function bi_str2vec(s,len) {
 var v=[], i=0, k;
 if (s.charAt(0)=='-') s=s.substring(1); 
 for (k=s.length; k>0; k-=7) v[i++] = s.substring(k-7,k)-0;
 v[i++]=0;
 if (len != null) while (i<len) v[i++]=0; 
 return v;
}

function bi_str2vec_(s,v) { // re-populates an existing vector v 
 var i,k;
 if (s.charAt(0)=='-') s=s.substring(1);
 for (i=0,k=s.length; k>0; k-=7,i++) v[i] = s.substring(k-7,k)-0;
 while (i<v.length) {v[i]=0; i++}
}

function bi_vec2str(v) {
 var r=[];
 for (var i=0;i<v.length;i++) {
  if (v[i]>=bi_RADIX) {v[i+1] += Math.floor(v[i]*bi_RADINV); v[i]=v[i]%bi_RADIX;}
  r[i] = (''+(bi_RADIX+v[i])).substring(1);
 }
 return bi_trim0(r.reverse().join(''));
}

//returns a duplicate of bigInt x
function bi_dup(x) {
  var buff=new Array(x.length);
  bi_copy_(buff,x);
  return buff;
}

//do x=y on bigInts x and y.  x must be an array at least as big as y (not counting the leading zeros in y).
function bi_copy_(x,y) {
 var i, xL = x.length, k = Math.min(xL, y.length);
 for (i=0; i<k; i++) x[i]=y[i];
 for (i=k; i<xL;i++) x[i]=0;
}

function bi_copyInt_(x,n) {
 x[0] = n%bi_RADIX;
 x[1] = Math.floor(n*bi_RADINV);
 for (var i=x.length-1; i>1; i--) x[i]=0;
}

function bi_GCD(x1,x2) {  // "integer" strings x1,x2
 var x1 = vld(x1), s1 = sgn(x1), a1 = abv(x1), v1=bi_str2vec(a1);
 var x2 = vld(x2), s2 = sgn(x2), a2 = abv(x2), v2=bi_str2vec(a2);

 if (s1*s2==0) return 'GCD(x,y) is the greatest common divisor of x and y. \nGCD(x,y) is not defined for zero input.'
 if (a1.length<a2.length || a1.length==a2.length && a1<a2) {
  bi_GCD_(v2,v1);
  return bi_vec2str(v2);
 }
 bi_GCD_(v1,v2);
 return bi_vec2str(v1);
}

// Set x to the greatest common divisor of vectors x and y; y is destroyed.
// This is an implementation of the classical Euclidean algorithm.
function bi_GCD_(x, y) {
 var t=0, T = bi_dup(x);
 while (y[1] || bi_hod(y)) { // while y[i]!=0 for some i>0
  bi_mod_(x, y);
  bi_copy_(T, x);
  bi_copy_(x, y);
  bi_copy_(y, T);
 }
 if (y[0] == 0) return;
 t = bi_modIntV(x, y[0]);
 bi_copyInt_(x, y[0]);
 y[0] = t;
 while (y[0]) { t = x[0] % y[0]; x[0] = y[0]; y[0] = t; }
}


function bi_modIntV(v,n) {  // a vector v and a number n<10000000, both positive
 var c=1, r=0;
 for (var i=0; i<v.length; i++) { 
  r = (r+c*v[i])%n;
  c = (c*bi_RADIX)%n;
 }
 return r;
}

// bi_mod_ called from bi_GCD_
function bi_mod_(x,y) { // input vectors x,y; result returned in x
 var q = new Array(x.length); //bi_copyInt_(q,0);
 var r = new Array(x.length); //bi_copyInt_(r,0);
 bi_divide_ (x,y,q,r) 
 bi_copy_(x,r);
}

function bi_sqrmod(v1,v2) { // unsigned "integer" strings v1,v2
 var m, a1 = abv(v1), a2 = abv(v2), n1=parseInt(a1,10), n2=parseInt(a2,10);

 if (a2==0) return 'Cannot divide by zero.'

 if (n1*n1 <= bi_MAXINT) {
  if (n2 <= bi_MAXINT) return ((n1*n1)%n2).toString();
  else                 return (n1*n1).toString();
 }
 if (2*a1.length < a2.length) return bi_square(a1);

 m = bi_square( bi_modU(a1, a2) );
 return bi_modU(m, a2);
}


function bi_modU(a1,a2) { // unsigned "integer" strings
 var L1=a1.length, k=a2.length, c=1, r=0, b, d, n2;
 if (a2==0)       return 'Cannot divide by zero.'
 if (less(a1,a2)) return a1;
 if (a1==a2)      return '0';
 if (k < 15) {
  n2 = 1*a2;
  for (var i=0; i<L1; i++) { r = (r+c*a1.charAt(L1-i-1))%n2; c = (c*10)%n2; }
  return r.toString();
 }
 if (a1.length <= k+1) {
  r = subtractUntilLess(a1,a2);
  return r;
 }
 var x = bi_str2vec(a1,2);
 var y = bi_str2vec(a2,2);
 var q = new Array(x.length); //bi_copyInt_(q,0);
 var r = new Array(x.length); //bi_copyInt_(r,0);
 bi_divide_ (x,y,q,r) 
 return bi_vec2str(r);
}

function bi_divide_ (x,y,q,r) {  // modified HAC Algorithm 14.20 taking advantage of FPU
 var i,j,n,t,d,qj;
 if (bi_zero(y)) return;  // 'Cannot divide by zero.'

 if (bi_equalV(x,y))        { bi_copyInt_(q,1); bi_copyInt_(r,0); return; }
 if (bi_hod(y)==0 && y[0]==1) { bi_copy_(q,x); bi_copyInt_(r,0); return; }

 bi_copyInt_(q,0);
 bi_copy_(r,x);

 if (less_(x,y)) return;

 n=bi_hod(x); // n = index of x's most significant "digit"
 t=bi_hod(y); // t = index of y's most significant "digit"

 r[-1] = 0; r[-2] = 0; y[-1] = 0;

 d = 1.0 / (bi_RADIX*y[t] + y[t-1]);

 j = n-t;
 qj = Math.floor((bi_RADIX*r[n] + r[n-1] + bi_RADINV*r[n-2]) * d);
 if (qj>=bi_RADIX) qj=bi_RADIX-1;

 if (qj) bi_linCombShift_(r,y,-qj,j); 

 while (bi_negativeOrNaN(r)) { qj--; bi_copy_(r,x); bi_linCombShift_(r,y,-qj,j);}
 while (!bi_less_shf(r,y,j)) { qj++; bi_subShift_(r,y,j); }
 q[j]=qj;

 for (i=n;i>t;i--) {
  j=i-t-1;
  qj = Math.floor(0.000000003+(bi_RADSQR*r[i] + bi_RADIX*r[i-1] + r[i-2]) * d);
  if (qj>=bi_RADIX) qj=bi_RADIX-1;

  bi_linCombShift_(r,y,-qj,j); 
  if (isNaN(r[r.length-1]) || r[r.length-1]<0) {
   bi_addShift_(r,y,j); qj--;
  }
  q[j]=qj;
 }
 delete r[-1]; delete r[-2]; delete y[-1];
}

function bi_addShift_(x,y,ys) {
  var i,c,k,xL=x.length,yL=y.length,k=Math.min(xL,yL+ys);

  for (c=0,i=ys;i<k;i++) {
    c+=x[i]+y[i-ys];
    x[i]=c%bi_RADIX;
    c=Math.floor(c*bi_RADINV);
  }
  for (i=k; c && i<xL; i++) {
    c+=x[i];
    x[i]=c%bi_RADIX;
    c=Math.floor(c*bi_RADINV);
  }
}

function bi_subShift_(x,y,ys) { // x,y nonnegative;
 var i,c,xL=x.length,yL=y.length,k=Math.min(xL,yL+ys);

 for (c=0,i=ys;i<k;i++) {
  c+=x[i]-y[i-ys];
  if (c<0) {c+bi_RADIX; x[i+1]--;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
 for (i=k; c && i<xL; i++) {
  c+=x[i];
  if (c<0) {c+bi_RADIX; x[i+1]--;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
 // For negatives only: must go on borrowing
 for ( ;x[i]<0 && i<xL-1; i++) { x[i]+=bi_RADIX; x[i+1]--; }
}

function bi_less_shf(x,y,ys) { // x,y nonnegative; y not zero; returns (x < y*RADIX^ys)
  var i, xL=x.length, yL=y.length, k=(xL<yL+ys?xL:yL+ys);  //k=Math.min(xL,yL+ys);

  for (i=k;    i<xL; i++) if (x[i]>0) return 0;
  for (i=k-ys; i<yL; i++) if (y[i]>0) return 1;
  for (i=k-1; i>=ys; i--) {
    if (x[i]>y[i-ys]) return 0;
    if (x[i]<y[i-ys]) return 1;
  } 
  return 0;
}

function bi_linCombShift_(x,y,b,ys) {  // let x = x + b*y*RADIX^ys
 var i, j, c=0, xL=x.length, yL=y.length, k=Math.min(xL,yL+ys);

 for (i=ys;i<k;i++) {
  c+=x[i]+b*y[i-ys];
  if (c<0) {j=Math.ceil(-c*bi_RADINV); c+=j*bi_RADIX; x[i+1]-=j;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
 for (i=k;c && i<xL;i++) {
  c+=x[i];
  if (c<0) {j=Math.ceil(-c*bi_RADINV); c+=j*bi_RADIX; x[i+1]-=j;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
 // For negatives only: must go on borrowing
 for ( ;x[i]<0 && i<xL-1; i++) { x[i]+=bi_RADIX; x[i+1]--; }
}

function bi_zero(x) {
 for (var i=x.length-1;i>=0;i--) if (x[i]) return 0;
 return 1;
}

function bi_negative(x) {
 if (x[x.length-1]<0) return 1;
 return 0;
}

function bi_negativeOrNaN(x) {
 if (isNaN(x[x.length-1]) || x[x.length-1]<0) return 1;
 return 0;
}

function bi_equalV(x,y) { // vectors x,y
  var i, xL=x.length, yL=y.length, k=(xL<yL?xL:yL);
  for (i=0;i<k;i++) if (x[i]!=y[i]) return 0;
  if (xL>yL) { for (;i<xL;i++) if (x[i]) return 0;} 
  else       { for (;i<yL;i++) if (y[i]) return 0;}
  return 1;
}

function bi_hod(x) { // the high-order digit (most significant element) of x
 for (var i=x.length-1;i>0;i--) if (x[i]) return i;
 return 0;
}

//--------------------------------------------------------------------
// Below is most of the Miller-Rabin-related code


function bi_millerRabinInt (n,a) {  // n string, a integer
 var k=n.length-1, d = parseInt(n.charAt(k));

 // Enforce MR test's precondition: large odd positive n
 if (n.charAt(0)=='-')          return 0; // input is negative
 if (isNaN(d) || k>0 && d%2==0) return 0; // NaN or even, not prime

 if (k<=0) {                              // single digits:
   if  (d==2||d==3||d==5||d==7) return 1; // 2,3,5,7 are primes
   else                         return 0; // others are not
 }
 var v = bi_str2vec(n);
 var mr_a=bi_dup(v);
 bi_copyInt_(mr_a,a);
 return bi_millerRabinV(v,mr_a);
}


function bi_millerRabin (n,a) {     // n,a both strings
 var k=n.length-1, d = parseInt(n.charAt(k));

 // Enforce MR test's precondition: large odd positive n
 if (n.charAt(0)=='-')          return 0; // input is negative
 if (isNaN(d) || k>0 && d%2==0) return 0; // NaN or even, not prime

 if (k<=0) {                              // single digits:
   if  (d==2||d==3||d==5||d==7) return 1; // 2,3,5,7 are primes
   else                         return 0; // others are not
 }
 
 var s = n.toString();
 var v = bi_str2vec(s);
 var b = bi_str2vec(a);

 return bi_millerRabinV (v,b);
}


function bi_millerRabinIntV(x,b) {  //x vector, b integer, with b<x
  var mr_a=bi_dup(x);
  bi_copyInt_(mr_a,b);
  return bi_millerRabinV(x,mr_a);
}


function bi_millerRabinV(x,b) {    // x,b are vectors, with b<x
  var i,j,k,s, mr_x1, mr_r, mr_a;

  mr_r = bi_trimV(x,0);
  mr_a = bi_dup(mr_r);
  bi_copy_(mr_a,b);
  bi_addInt_(mr_r,-1);
  mr_x1=bi_dup(mr_r);

  if (bi_zero(mr_r)) return 0;   // input x was 1!

  //s=the highest power of two that divides mr_r
  s=0; while (0==bi_divInt_(mr_r,2)) s++;
  if (!s) return 0;              // input x was even!

  bi_multInt_(mr_r,2); mr_r[0]++;   // mr_r = mr_r*2 + 1
  bi_powMod_(mr_a,mr_r,x);

  if (!bi_equalsInt(mr_a,1) && !bi_equalV(mr_a,mr_x1)) {
    j=1;
    while (j<=s-1 && !bi_equalV(mr_a,mr_x1)) {
      bi_squareMod_(mr_a,x);
      if (bi_equalsInt(mr_a,1)) {
        return 0;
      }
      j++;
    }
    if (!bi_equalV(mr_a,mr_x1)) {
      return 0;
    }
  }
  return 1;  
}

//do x=x**y mod n, where x,y,n are bigInts and ** is exponentiation.  0**0=1.
//this is faster when n is odd.  x usually needs to have as many elements as n.
function bi_powMod_(x,y,n) {
  var i,k1,k2,kn,np,bits=[];
  var s7=bi_dup(n);
  var yc=bi_dup(y);

  // For an even modulus or (for radix 10^k) a modulus divisible by 5,  
  // the radix and modulus are not necessarily coprime.
  // Therefore we cannot use the faster Montgomery algorithm,
  // so we use a simple square-and-multiply algorithm.

  if ((n[0]&1)==0 || n[0]%5==0) {
    bi_copy_(s7,x);
    bi_copyInt_(x,1);
    while(!bi_equalsInt(yc,0)) {
      if (yc[0]&1)
        bi_multMod_(x,s7,n);
      bi_divInt_(yc,2);
      bi_squareMod_(s7,n); 
    }
    return;
  }

  //calculate np from n for the Montgomery multiplications
  bi_copyInt_(s7,0);
  for (kn=n.length; kn>0 && !n[kn-1]; kn--);

  var m = bi_modInt(n,bi_RADIX);
  var i = bi_invModInt(m,bi_RADIX);  // this i may be negative

  if (i<0)        i+=bi_RADIX*Math.ceil(-i/bi_RADIX);
  if (i>bi_RADIX) i-=bi_RADIX*Math.floor(i/bi_RADIX);

  np=bi_RADIX-i;

  s7[kn]=1;
  bi_multMod_(x,s7,n);   // x = x * RADIX**(kn) mod n

  var s3=bi_dup(x);
  k1 = bi_hod(y);     // k1 = the high-order digit element of y
  if (y[k1]==0) {     //anything to the 0th power is 1
    bi_copyInt_(x,1);
    return;
  }

  // Algorithm 14.94 (HAC)

  var i=0;  while(!bi_equalsInt(yc,0)) bits[i++] = bi_divInt_(yc,2);
  for (i=bits.length-1; i>0; i--) {
   bi_mont_(x,x,n,np);
   if (bits[i-1]) bi_mont_(x,s3,n,np);
  }
  bi_mont_(x,bi_ONE,n,np);
  return;
}

// do x=x*y*Ri mod n for bigInts x,y,n, 
//  where Ri = radix**(-kn) mod n, and kn is the 
//  number of elements in the n array, not 
//  counting leading zeros.  
// x array must have at least as many elemnts as the n array
// It's OK if x and y are the same variable.
// must have:
//  x,y < n
//  n is odd
//  np = -(n^(-1)) mod radix

sa = new Array(0); // scratchpad array (global for speed)

function bi_mont_(x,y,n,np) {
  var i,j,c,ui,t,ks,ky4,kn4;
  var kn=n.length;
  var ky=y.length;

  for (;kn>0 && n[kn-1]==0;kn--); //ignore leading zeros of n
  for (;ky>0 && y[ky-1]==0;ky--); //ignore leading zeros of y

  ky4 = ky-4;
  kn4 = kn-4;

  if (sa.length!=kn)
    sa=new Array(kn);

  bi_copyInt_(sa,0);

  ks=sa.length-1; //sa will never have more than this many nonzero elements.  

  //the following loop consumes 95% of runtime for large numbers
  for (i=0; i<kn; i++) {
    t=sa[0]+x[i]*y[0];
    ui=((t % bi_RADIX) * np) % bi_RADIX;  
    c = Math.floor((t+ui*n[0])*bi_RADINV);
    t=x[i];
    
    //do sa=(sa+x[i]*y+ui*n)/b  where b=10000000.  Loop is unrolled 5-fold for speed
    j=1;

    for (;j<ky4;)  { c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++; }    
    for (;j<ky;)   { c+=sa[j]+ui*n[j]+t*y[j]; sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++; }
    for (;j<kn4;)  { c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++;
                     c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++; }  
    for (;j<kn;)   { c+=sa[j]+ui*n[j];        sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++; }   
    for (;j<ks;)   { c+=sa[j];                sa[j-1]=c % bi_RADIX; c=Math.floor(c*bi_RADINV); j++; }  
    sa[j-1]=c % bi_RADIX;
  }

  if (!bi_greater(n,sa)) bi_sub_(sa,n);
  bi_copy_(x,sa);
}


function bi_equalsInt(x,y) {
  if (x[0]!=y) return 0;
  for (var i=1;i<x.length;i++) if (x[i]) return 0;
  return 1;
}


//return x**(-1) mod n, for integers x and n. Return 0 if there is no inverse
function bi_invModInt(x,n) {
  var a=1,b=0;
  for (;;) {
    if (x==1) return a;
    if (x==0) return 0;
    b-=a*Math.floor(n/x);
    n%=x;

    if (n==1) return b; 
    if (n==0) return 0;
    a-=b*Math.floor(x/n);
    x%=n;
  }
}

//is x > y? (x and y both nonnegative)
function bi_greater(x,y) {
  var i;
  var k=Math.min(x.length,y.length);

  for (i=x.length;i<y.length;i++) if (y[i]) return 0;  //y has more digits
  for (i=y.length;i<x.length;i++) if (x[i]) return 1;  //x has more digits

  for (i=k-1;i>=0;i--)
    if (x[i]>y[i])      return 1;
    else if (x[i]<y[i]) return 0;
  return 0;
}


function bi_sub_(x,y) {
 var i,j,c,k=Math.min(x.length,y.length);

 for (c=0,i=0;i<k;i++) {
  c+=x[i]-y[i];
  if (c<0) {j=Math.ceil(-c*bi_RADINV); c+=j*bi_RADIX; x[i+1]-=j;}
  x[i]=c % bi_RADIX;
  c = Math.floor(c*bi_RADINV);
 }
 for (i=k;c && i<x.length;i++) {
  c+=x[i];
  x[i]=c % bi_RADIX;
  c = Math.floor(c*bi_RADINV);
 }
 // For negatives only: must go on borrowing
 for ( ;x[i]<0 && i<k-1; i++) { x[i]+=bi_RADIX; x[i+1]--; }
}

//do x=x*y mod n for bigInts x,y,n.
//for greater speed, let y<x.
function bi_multMod_(x,y,n) {
  var i, s0=new Array(2*x.length);
  bi_copyInt_(s0,0);
  for (i=0;i<y.length;i++)
    if (y[i])
      bi_linCombShift_(s0,x,y[i],i);  
  bi_mod_(s0,n);
  bi_copy_(x,s0);
}

//do x=x*x mod n for bigInts x,n.
function bi_squareMod_(x,n) {
  var i,j,c,kx,k,xi,m=0;
  for (kx=x.length; kx>0 && !x[kx-1]; kx--);  //ignore leading zeros in x
  k=kx>n.length ? 2*kx : 2*n.length; //k elements in the product, twice as many as in the larger of x and n

  var s0=new Array(k);
  bi_copyInt_(s0,0);
  for (i=0;i<kx;i++) {
    xi = x[i];
    c=s0[m]+xi*xi;
    s0[m]=c % bi_RADIX;
    c=Math.floor(c*bi_RADINV);
    xi += xi;
    for (j=i+1;j<kx;j++) {
      c=s0[i+j]+xi*x[j]+c;
      s0[i+j]=c % bi_RADIX;
      c=Math.floor(c*bi_RADINV);
    }
    s0[i+kx]=c;
    m+=2;
  }
  bi_mod_(s0,n);
  bi_copy_(x,s0);
}


//return x with exactly k leading zero elements
function bi_trimV(x,k) {
 var i,y;
 for (i=x.length; i>0 && !x[i-1]; i--);
 y=new Array(i+k);
 bi_copy_(y,x);
 return y;
}

function bi_multInt_(x,n) {
 var i, j, c=0, k=x.length;
 if (!n) return;

 for (i=0;i<k;i++) {
  c+=x[i]*n;
  if (c<0) {j=Math.ceil(-c*bi_RADINV); c+=j*bi_RADIX; x[i+1]-=j;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
}

function bi_addInt_(x,n) {
 var i, j, c=n, k=x.length;

 for (i=0; c && i<k;i++) {
  c+=x[i];
  if (c<0) {j=Math.ceil(-c*bi_RADINV); c+=j*bi_RADIX; x[i+1]-=j;}
  x[i]=c%bi_RADIX;
  c=Math.floor(c*bi_RADINV);
 }
 // For negatives only: must go on borrowing
 for ( ;x[i]<0 && i<k-1; i++) { x[i]+=bi_RADIX; x[i+1]--; }
}

function bi_divInt_(x,n) {
 var i,r=0,s;
 for (i=x.length-1;i>=0;i--) {
  s=r*bi_RADIX+x[i];
  x[i]=Math.floor(s/n);
  r=s%n;
 }
 return r;
}

//return x mod n (vector x, integer n)
function bi_modInt(x,n) {
 var i,c=0;
 for (i=x.length-1; i>=0; i--) c=(c*bi_RADIX+x[i])%n;
 return c;
}


//-----------------------------------------------------

// Higher-level functions using the Miller-Rabin test


function bi_isPrimeMR(n) {
 var a, s = vld(n);
 var smallPrimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113];

 if (less(n,'2'))  return 0; 
 if (s.length>500) return 'Primality check will take too long.'

 for (var k=0;k<smallPrimes.length;k++) {
  a = smallPrimes[k];
  if (s==a+'') return 1;
  if (bi_millerRabinInt(s,a)==0) return 0;
 }
 return 1;
}

function bi_nextPrimeMR(n) {
 var r, s = vld(n), f=parseFloat(s);
 var len=s.length, d=parseInt(s.charAt(len-1),10);
 if (less(s,'2')) return '2'
 if (f<3)  return '3'
 if (f<5)  return '5'
 if (f<7)  return '7'
 if (f<11) return '11'
 if (f<13) return '13'

 if (s.length>500) return 'Primality check will take too long.'

 if (d%2) r = bi_addU(s,'2');
 else     r = bi_addU(s,'1');

 while (divisibleBy3or5or7or11or13(r) || !bi_isPrimeMR(r)) { 
  if (r.charAt(r.length-1)==3) r=bi_addU(r,'4');
  else                         r=bi_addU(r,'2');
 }
 return r;
}

function bi_prevPrimeMR(n) {
 var r, s = vld(n), f=parseFloat(s);
 var len=s.length, d=parseInt(s.charAt(len-1),10);

 if (s.charAt(0)=='-' 
  || f<=2)  return 'There are no primes less than 2.'
 if (f<=3)  return '2'
 if (f<=5)  return '3'
 if (f<=7)  return '5'
 if (f<=11) return '7'
 if (f<=13) return '11'
 if (f<=17) return '13'

 if (s.length>500) return 'Primality check will take too long.'

 if (d%2) r = bi_subU(s,'2');
 else     r = bi_subU(s,'1');

 while (divisibleBy3or5or7or11or13(r) || !bi_isPrimeMR(r)) {
  if (r.charAt(r.length-1)==7) r=bi_subU(r,'4');
  else                         r=bi_subU(r,'2');
 }
 return r;
}


//----------------------------------------------------------------
// FIX 20121008 - call BigInt.js with the fix described at
// www.javascripter.net/math/primes/millerrabinbug-bigint54.htm

function bin_millerRabin (n,a) {          // n,a both strings
 var k=n.length-1, d = parseInt(n.charAt(k));

 // Enforce MR test's precondition: large odd positive n
 if (n.charAt(0)=='-')          return 0; // input is negative
 if (isNaN(d) || k>0 && d%2==0) return 0; // NaN or even, not prime

 if (k<=0) {                              // single digits:
   if  (d==2||d==3||d==5||d==7) return 1; // 2,3,5,7 are primes
   else                         return 0; // others are not
 }

 var s = n.toString(), len=s.length;
 var v = str2bigInt(s, 10, len);
 var b = str2bigInt(a, 10, len);

 return millerRabin (v,b); // uses BigInt.js millerRabin
}


function isPrimeMR(n) {
 var smallPrimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113];
 var a, b, s = vld(n), len=s.length, f=parseFloat(s);

 if (s.charAt(0)=='-' || f<2) return 0;

 b = str2bigInt(s,10,len);

 for (var k=0;k<30;k++) {
  a = smallPrimes[k];
  if (s==''+a) return 1;
  if (millerRabinInt(b,a)==0) return 0;
 }
 return 1;
}

function nextPrimeMR(n) {
 var r, s = vld(n), f=parseFloat(s);
 var len=s.length, d=parseInt(s.charAt(len-1),10);
 if (less(s,'2')) return '2'
 if (f<3)  return '3'
 if (f<5)  return '5'
 if (f<7)  return '7'
 if (f<11) return '11'
 if (f<13) return '13'

 if (s.length>500) return 'Primality check will take too long.'

 if (d%2) r = bi_addU(s,'2');
 else     r = bi_addU(s,'1');

 while (divisibleBy3or5or7or11or13(r) || !isPrimeMR(r)) { 
  if (r.charAt(r.length-1)==3) r=bi_addU(r,'4');
  else                         r=bi_addU(r,'2');
 }
 return r;
}

function prevPrimeMR(n) {
 var r, s = vld(n), f=parseFloat(s);
 var len=s.length, d=parseInt(s.charAt(len-1),10);

 if (s.charAt(0)=='-' 
  || f<=2)  return 'There are no primes less than 2.'
 if (f<=3)  return '2'
 if (f<=5)  return '3'
 if (f<=7)  return '5'
 if (f<=11) return '7'
 if (f<=13) return '11'
 if (f<=17) return '13'

 if (s.length>500) return 'Primality check will take too long.'

 if (d%2) r = bi_subU(s,'2');
 else     r = bi_subU(s,'1');

 while (divisibleBy3or5or7or11or13(r) || !isPrimeMR(r)) {
  if (r.charAt(r.length-1)==7) r=bi_subU(r,'4');
  else                         r=bi_subU(r,'2');
 }
 return r;
}



