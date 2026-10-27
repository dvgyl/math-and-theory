import fs from 'node:fs';

// Independent exact checker.  Native BigInt arithmetic; polynomials are
// constructed directly in sorted-gap coordinates.  No transfer-matrix powers
// and no conversion from raw weight variables are used here.
class P {
  constructor(d=0) { this.d=d; this.v=Array((d+1)*(d+2)/2).fill(0n); }
  idx(i,j) { return i*(this.d+1)-i*(i-1)/2+j; }
  get(i,j) { return this.v[this.idx(i,j)]; }
  set(i,j,v) { this.v[this.idx(i,j)]=v; }
}
function constant(x) { let p=new P(); p.v[0]=BigInt(x); return p; }
function add(p,q,s=1n) {
  if(p.d!==q.d) throw Error('degree mismatch');
  let r=new P(p.d);
  for(let i=0;i<r.v.length;i++) r.v[i]=p.v[i]+s*q.v[i];
  return r;
}
function times(p,s) {let r=new P(p.d);r.v=p.v.map(x=>x*s);return r;}
function mul(p,q) {
  let r=new P(p.d+q.d),terms=[];
  for(let i=0;i<=q.d;i++) for(let j=0;j<=q.d-i;j++) {
    let v=q.get(i,j);if(v!==0n)terms.push([i,j,v]);
  }
  for(let i=0;i<=p.d;i++) for(let j=0;j<=p.d-i;j++) {
    let v=p.get(i,j);if(v===0n)continue;
    for(let [k,l,w] of terms) r.v[r.idx(i+k,j+l)]+=v*w;
  }
  return r;
}
function traceNext(n,c,hist) {
  let m=c.length-1,r=new P(2*n);
  // Newton identities: p_n+c1*p_(n-1)+...+c_(n-1)*p1+n*cn=0.
  for(let j=1;j<=Math.min(m,n-1);j++)
    r=add(r,mul(hist[n-j],c[j]),-1n);
  if(n<=m)r=add(r,c[n],-BigInt(n));
  // For n>m the loop above already includes the final term c_m*p_(n-m).
  return r;
}

let N=Number(process.argv[2]??69),results=[];
if(process.argv.length>3||!Number.isSafeInteger(N)||N<3) {
  throw Error('Require one integer maximum order of at least three.');
}
// Reflection interchanges a and c.  These three orders therefore cover all six.
let ranks=[[0,1,2],[1,0,2],[0,2,1]];
for(let chamber=0;chamber<3;chamber++) {
  let weights=ranks[chamber].map(rank=>{
    let p=new P(1);p.set(0,0,1n);
    if(rank>=1)p.set(1,0,1n);
    if(rank>=2)p.set(0,1,1n);
    return p;
  });
  let [a,b,c]=weights;
  let aa=mul(a,a),bb=mul(b,b),cc=mul(c,c),f=mul(a,c);
  let d=add(add(aa,bb),cc),e=mul(b,add(a,c));
  let ff=mul(f,f),f4=mul(ff,ff),f6=mul(f4,ff),ee=mul(e,e);
  // Characteristic polynomials of the two transfer blocks, obtained by
  // independent signed-permutation determinant expansion.
  let h1=[constant(1),times(e,-1n),times(mul(d,f),-1n),
          times(mul(e,ff),-1n),times(f4,-1n)];
  let h2=[constant(1),times(d,-1n),times(add(ee,ff),-1n),
          times(mul(ee,f),-2n),times(add(mul(ee,ff),f4),-1n),
          mul(d,f4),f6];
  let s1=[constant(4)],s2=[constant(6)];
  let ap=constant(1),cp=constant(1),fp=constant(1);
  let u0=constant(2),v0=constant(2),w0=constant(2);
  let u1=add(bb,f,2n),v1=mul(a,b),w1=mul(c,b);
  let ru=add(bb,f,2n),rv=mul(a,b),rw=mul(c,b);
  let sv=mul(aa,f),sw=mul(cc,f),fact=1n;
  for(let n=1;n<=N;n++) {
    fact*=BigInt(n);ap=mul(ap,aa);cp=mul(cp,cc);fp=mul(fp,f);
    let u,v,w;
    if(n===1){u=u1;v=v1;w=w1;}
    else {
      u=add(mul(u1,ru),mul(u0,ff),-1n);
      v=add(mul(v1,rv),mul(v0,sv));
      w=add(mul(w1,rw),mul(w0,sw));
      [u0,u1]=[u1,u];[v0,v1]=[v1,v];[w0,w1]=[w1,w];
    }
    // If lambda_± are the roots of x²-bx-ac, these sequences are
    // u=lambda_+^(2n)+lambda_-^(2n),
    // v=(a lambda_+)^n+(a lambda_-)^n, and similarly for w,c.
    let psq=add(add(add(add(ap,cp),u),v,2n),w,2n);
    if(n%2===0)psq=add(psq,fp,4n);
    s1.push(traceNext(n,h1,s1));s2.push(traceNext(n,h2,s2));
    let gram=add(add(s2.at(-1),s1.at(-1),2n),fp,2n);
    if(n<3)continue;
    const positions=(2*n+1)*(2*n+2)/2;
    if(psq.d!==2*n||gram.d!==2*n||psq.v.length!==positions||gram.v.length!==positions) {
      throw Error(`Incomplete coefficient vector at order ${n}, chamber ${chamber}.`);
    }
    let factor=BigInt(n)**BigInt(n),min=null,positive=0,zero=0,negative=0;
    for(let k=0;k<psq.v.length;k++) {
      let z=factor*psq.v[k]-fact*gram.v[k];
      if(z<0n)negative++;
      else if(z===0n)zero++;
      else{positive++;if(min===null||z<min)min=z;}
    }
    let record={n,chamber,a_b_c_ranks:ranks[chamber],positive,zero,negative,
                min_positive:String(min)};
    results.push(record);
    if(negative)throw Error(`negative coefficient: ${JSON.stringify(record)}`);
    if(n===3||n===4||n%10===0||n===N)console.log(JSON.stringify(record));
  }
}
const keys=new Set(results.map(r=>`${r.n},${r.chamber}`));
if(results.length!==3*(N-2)||keys.size!==results.length) {
  throw Error('Incomplete or duplicate finite certificate coverage.');
}
for(let n=3;n<=N;n++) for(let chamber=0;chamber<3;chamber++) {
  if(!keys.has(`${n},${chamber}`)) throw Error('Missing finite certificate chamber.');
}
fs.writeFileSync('independent_finite.json',JSON.stringify({
  status:'passed',
  algorithm:'Newton identities and direct gap-coordinate recurrences',
  arithmetic:'native JavaScript BigInt, exact integers',max_n:N,results
},null,2)+'\n');
