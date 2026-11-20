/* Independent verifier: recompute a(n) mod q by direct modular exponentiation (no discrete logs),
   check q prime, q == 1 mod ell, A != 0 and A^((q-1)/ell) != 1 mod q, and check coverage of all
   n in [N_LO, ell] for every prime ell in [ELL_LO, ELL_HI]. Reads certificate lines "ell q n1 n2 ...". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a,uint64_t b,uint64_t m){return (u128)a*b%m;}
static uint64_t powmod(uint64_t a,uint64_t e,uint64_t m){uint64_t r=1%m;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int isprime_trial(uint64_t n){ if(n<2) return 0; for(uint64_t p=2;p*p<=n;p++) if(n%p==0) return 0; return 1; } /* trial division: independent of MR */
int main(int argc,char**argv){
  long ELL_LO=atol(argv[1]), ELL_HI=atol(argv[2]), N_LO=atol(argv[3]);
  FILE*f=fopen(argv[4],"r");
  static char line[1<<22];
  char *covered=calloc(ELL_HI+2,1); long cur_ell=-1; long pairs=0, bad=0, ells=0;
  uint64_t *fi=malloc(sizeof(uint64_t)*(ELL_HI+2)), *Fm=malloc(sizeof(uint64_t)*(ELL_HI+2));
  long *seen_ell=calloc(ELL_HI+2,sizeof(long));
  // coverage map per ell: we process lines grouped by ell (file is ordered)
  char *cov=calloc(ELL_HI+2,1);
  while(fgets(line,sizeof line,f)){
    char*p=line; long ell=strtol(p,&p,10); uint64_t q=strtoull(p,&p,10);
    if(ell!=cur_ell){
      if(cur_ell>0){ for(long n=N_LO;n<=cur_ell;n++) if(!cov[n]){ printf("UNCOVERED ell=%ld n=%ld\n",cur_ell,n); bad++; } }
      cur_ell=ell; memset(cov,0,ELL_HI+2); ells++; seen_ell[ell]=1;
      if(!isprime_trial(ell)){ printf("ell not prime %ld\n",ell); bad++; }
    }
    if(!isprime_trial(q) || (q-1)%ell!=0){ printf("bad q %llu for ell %ld\n",(unsigned long long)q,ell); bad++; continue; }
    fi[1]=1%q; for(long i=2;i<=ell;i++) fi[i]=mulmod(fi[i-1],i,q);
    Fm[1]=1%(q-1); for(long m=2;m<=ell;m++) Fm[m]=mulmod(Fm[m-1],m,q-1);
    while(1){ while(*p==' ') p++; if(*p=='\n'||*p==0) break; long n=strtol(p,&p,10);
      if(n<N_LO||n>ell){ printf("n out of range\n"); bad++; continue; }
      uint64_t s=0; for(long i=1;i<=n;i++){ s+=powmod(fi[i],Fm[n-i+1],q); if(s>=q) s-=q; }
      if(s==0 || powmod(s,(q-1)/ell,q)==1){ printf("FAIL ell=%ld q=%llu n=%ld\n",ell,(unsigned long long)q,n); bad++; }
      else { if(!cov[n]) pairs++; cov[n]=1; }
    }
  }
  if(cur_ell>0){ for(long n=N_LO;n<=cur_ell;n++) if(!cov[n]){ printf("UNCOVERED ell=%ld n=%ld\n",cur_ell,n); bad++; } }
  // every prime ell in range must appear
  for(long e=(ELL_LO>N_LO?ELL_LO:N_LO); e<=ELL_HI; e++) if(isprime_trial(e) && !seen_ell[e]){ printf("MISSING ell=%ld\n",e); bad++; }
  printf("ells=%ld verified_pairs=%ld bad=%ld\n",ells,pairs,bad);
  return bad!=0;
}
