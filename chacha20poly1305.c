#define FOR(i,n) for (i = 0;i < n;++i)
#define sv static void

typedef unsigned char u8;
typedef unsigned long u32;
typedef unsigned long long u64;
typedef long long i64;

static u32 L32(u32 x,int c) { return (x << c) | ((x&0xffffffff) >> (32 - c)); }

static u32 ld32(const u8 *x)
{
  u32 u = x[3];
  u = (u<<8)|x[2];
  u = (u<<8)|x[1];
  return (u<<8)|x[0];
}

sv st32(u8 *x,u32 u)
{
  int i;
  FOR(i,4) { x[i] = u; u >>= 8; }
}

sv qr(u32 *x,int a,int b,int c,int d)
{
  x[a] += x[b]; x[d] ^= x[a]; x[d] = L32(x[d],16);
  x[c] += x[d]; x[b] ^= x[c]; x[b] = L32(x[b],12);
  x[a] += x[b]; x[d] ^= x[a]; x[d] = L32(x[d],8);
  x[c] += x[d]; x[b] ^= x[c]; x[b] = L32(x[b],7);
}

sv core(u8 *out,const u8 *in,const u8 *k,const u8 *c)
{
  u32 x[16],y[16];
  int i,j,m;

  FOR(i,4) {
    x[i] = ld32(c+4*i);
    x[4+i] = ld32(k+4*i);
    x[8+i] = ld32(k+16+4*i);
    x[12+i] = ld32(in+4*i);
  }

  FOR(i,16) y[i] = x[i];

  FOR(i,10) {
    qr(x,0,4, 8,12);
    qr(x,1,5, 9,13);
    qr(x,2,6,10,14);
    qr(x,3,7,11,15);
    qr(x,0,5,10,15);
    qr(x,1,6,11,12);
    qr(x,2,7, 8,13);
    qr(x,3,4, 9,14);
  }

  FOR(i,16) st32(out + 4 * i,x[i] + y[i]);
}

static const u8 sigma[16] = "expand 32-byte k";

int chacha20_encrypt(u8 *c,const u8 *m,u64 b,const u8 *n,const u8 *k)
{
  u8 z[16],x[64];
  u32 u,i;
  if (!b) return 0;
  FOR(i,4) z[i] = 0;
  FOR(i,12) z[i+4] = n[i];
  while (b >= 64) {
    core(x,z,k,sigma);
    FOR(i,64) c[i] = (m?m[i]:0) ^ x[i];
    u = 1;
    FOR(i,4) {
      u += (u32) z[i];
      z[i] = u;
      u >>= 8;
    }
    b -= 64;
    c += 64;
    if (m) m += 64;
  }
  if (b) {
    core(x,z,k,sigma);
    FOR(i,b) c[i] = (m?m[i]:0) ^ x[i];
  }
  return 0;
}

sv add1305(u32 *h,const u32 *c)
{
  u32 j,u = 0;
  FOR(j,17) {
    u += h[j] + c[j];
    h[j] = u & 255;
    u >>= 8;
  }
}

static const u32 minusp[17] = {
  5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252
} ;

int poly1305(u8 *out,const u8 *m,u64 n,const u8 *k)
{
  u32 s,i,j,u,x[17],r[17],h[17],c[17],g[17];

  FOR(j,17) r[j]=h[j]=0;
  FOR(j,16) r[j]=k[j];
  r[3]&=15;
  r[4]&=252;
  r[7]&=15;
  r[8]&=252;
  r[11]&=15;
  r[12]&=252;
  r[15]&=15;

  while (n > 0) {
    FOR(j,17) c[j] = 0;
    for (j = 0;(j < 16) && (j < n);++j) c[j] = m[j];
    c[j] = 1;
    m += j; n -= j;
    add1305(h,c);
    FOR(i,17) {
      x[i] = 0;
      FOR(j,17) x[i] += h[j] * ((j <= i) ? r[i - j] : 320 * r[i + 17 - j]);
    }
    FOR(i,17) h[i] = x[i];
    u = 0;
    FOR(j,16) {
      u += h[j];
      h[j] = u & 255;
      u >>= 8;
    }
    u += h[16]; h[16] = u & 3;
    u = 5 * (u >> 2);
    FOR(j,16) {
      u += h[j];
      h[j] = u & 255;
      u >>= 8;
    }
    u += h[16]; h[16] = u;
  }

  FOR(j,17) g[j] = h[j];
  add1305(h,minusp);
  s = -(h[16] >> 7);
  FOR(j,17) h[j] ^= s & (g[j] ^ h[j]);

  FOR(j,16) c[j] = k[j + 16];
  c[16] = 0;
  add1305(h,c);
  FOR(j,16) out[j] = h[j];
  return 0;
}

#include <stdio.h>
int chacha20poly1305_encrypt(u8 *k, u8 *n, u8 *ad, u64 adlen, u8 *m, u64 mlen) {
  u8 b[32];

  u8 key[]="\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f";
  u8 nonce[]="\x00\x00\x00\x00\x00\x01\x02\x03\x04\x05\x06\x07";
  chacha20_encrypt(b,NULL,sizeof(b),nonce,key);
  u32 i;
  FOR(i,32) printf("%02x",b[i]); printf("\n");
  return 0;
}

int main(void) {
  chacha20poly1305_encrypt(NULL,NULL,NULL,0,NULL,0);
}
