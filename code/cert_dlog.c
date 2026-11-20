/* Modular certificates for A113258.
   For each prime ell in [ELL_LO, ELL_HI] and each n in [N_LO, ell], find a prime q == 1 (mod ell)
   such that A = a(n) mod q is nonzero and NOT an ell-th power residue mod q, where
   a(n) = sum_{i=1}^n (i!)^{(n-i+1)!}.
   Method: discrete logs base a primitive root g of q.
   Output lines: "ell q n1 n2 ..." meaning q certifies those n (all n in [N_LO,ell] are covered). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a,uint64_t b,uint64_t m){return (u128)a*b%m;}
static uint64_t powmod(uint64_t a,uint64_t e,uint64_t m){uint64_t r=1%m;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int is_prime_u64(uint64_t n){ if(n<2)return 0; static const uint64_t sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for(int i=0;i<12;i++){ if(n%sp[i]==0) return n==sp[i]; }
  uint64_t d=n-1; int s=0; while(!(d&1)){d>>=1;s++;}
  for(int i=0;i<12;i++){ uint64_t a=sp[i]; uint64_t x=powmod(a,d,n); if(x==1||x==n-1) continue; int ok=0;
    for(int r=1;r<s;r++){ x=mulmod(x,x,n); if(x==n-1){ok=1;break;} } if(!ok) return 0; }
  return 1; }
static int factor_small(uint64_t n, uint64_t *ps){ int k=0; for(uint64_t p=2;p*p<=n;p++){ if(n%p==0){ ps[k++]=p; while(n%p==0) n/=p; } } if(n>1) ps[k++]=n; return k; }
static uint64_t primroot(uint64_t q){ uint64_t ps[64]; int k=factor_small(q-1,ps);
  for(uint64_t g=2;;g++){ int ok=1; for(int i=0;i<k;i++) if(powmod(g,(q-1)/ps[i],q)==1){ok=0;break;} if(ok) return g; } }
int main(int argc,char**argv){
  long ELL_LO=atol(argv[1]), ELL_HI=atol(argv[2]); long N_LO=atol(argv[3]);
  uint32_t *pw=NULL,*lg=NULL; size_t cap=0;
  uint64_t *d=malloc(sizeof(uint64_t)*(ELL_HI+2)), *E=malloc(sizeof(uint64_t)*(ELL_HI+2));
  uint64_t *A=malloc(sizeof(uint64_t)*(ELL_HI+2)); char *pend=malloc(ELL_HI+2);
  long total_pairs=0, total_q=0, max_tries=0;
  for(long ell=ELL_LO; ell<=ELL_HI; ell++){
    if(ell<N_LO || !is_prime_u64(ell)) continue;
    long npend=0; for(long n=N_LO;n<=ell;n++){pend[n]=1;npend++;} total_pairs+=npend;
    long tries=0;
    for(uint64_t k=1; npend>0; k++){
      uint64_t q=2*k*ell+1; if(!is_prime_u64(q)) continue; tries++; total_q++;
      if(q-1>cap){ cap=q; pw=realloc(pw,sizeof(uint32_t)*cap); lg=realloc(lg,sizeof(uint32_t)*cap); }
      uint64_t g=primroot(q); uint64_t x=1; for(uint64_t e=0;e<q-1;e++){ pw[e]=(uint32_t)x; lg[x]=(uint32_t)e; x=mulmod(x,g,q); }
      uint64_t Q1=q-1;
      // d[i] = dlog(i! mod q), E[m] = m! mod (q-1)
      d[1]=0; for(long i=2;i<=ell;i++) d[i]=(d[i-1]+lg[i])%Q1;
      E[1]=1%Q1; for(long m=2;m<=ell;m++) E[m]=mulmod(E[m-1],m,Q1);
      long certified_here=0; long list[1];
      printf("%ld %llu",ell,(unsigned long long)q);
      for(long n=N_LO;n<=ell;n++){ if(!pend[n]) continue;
        uint64_t s=0; for(long m=1;m<=n;m++){ uint64_t e=mulmod(d[n-m+1],E[m],Q1); s+=pw[e]; if(s>=q) s-=q; }
        A[n]=s;
        if(s!=0 && (lg[s]%ell)!=0){ pend[n]=0; npend--; certified_here++; printf(" %ld",n); }
      }
      printf("\n");
      if(tries>200){ fprintf(stderr,"too many tries ell=%ld\n",ell); return 1; }
    }
    if(tries>max_tries) max_tries=tries;
  }
  fprintf(stderr,"pairs=%ld q_used=%ld max_q_per_ell=%ld\n",total_pairs,total_q,max_tries);
  return 0;
}
