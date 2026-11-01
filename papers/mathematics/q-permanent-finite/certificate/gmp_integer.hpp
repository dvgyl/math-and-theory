#pragma once
// Minimal binding to the installed GMP 6.x integer ABI on this 64-bit platform.
// No GMP development headers are installed. These exported C entry points are
// independently exercised by the exhaustive-permutation checker before use.
#include <cmath>
#include <cstdlib>
#include <ostream>
#include <string>
#include <utility>
static_assert(sizeof(long)==8 && sizeof(void*)==8,"This local GMP binding requires a 64-bit Unix ABI");
extern "C" {
struct local_mpz {int alloc;int size;unsigned long* limbs;};
void __gmpz_init(local_mpz*);
void __gmpz_clear(local_mpz*);
void __gmpz_set(local_mpz*,const local_mpz*);
void __gmpz_set_si(local_mpz*,long);
void __gmpz_swap(local_mpz*,local_mpz*);
void __gmpz_add(local_mpz*,const local_mpz*,const local_mpz*);
void __gmpz_sub(local_mpz*,const local_mpz*,const local_mpz*);
void __gmpz_mul(local_mpz*,const local_mpz*,const local_mpz*);
void __gmpz_mul_si(local_mpz*,const local_mpz*,long);
void __gmpz_mul_ui(local_mpz*,const local_mpz*,unsigned long);
void __gmpz_addmul_ui(local_mpz*,const local_mpz*,unsigned long);
void __gmpz_submul_ui(local_mpz*,const local_mpz*,unsigned long);
unsigned long __gmpz_tdiv_q_ui(local_mpz*,const local_mpz*,unsigned long);
unsigned long __gmpz_tdiv_r_ui(local_mpz*,const local_mpz*,unsigned long);
int __gmpz_cmp(const local_mpz*,const local_mpz*);
int __gmpz_cmp_si(const local_mpz*,long);
char* __gmpz_get_str(char*,int,const local_mpz*);
double __gmpz_get_d_2exp(long*,const local_mpz*);
}

class Z {
public:
 local_mpz z;
 Z(){__gmpz_init(&z);}
 Z(long v):Z(){__gmpz_set_si(&z,v);}
 Z(const Z& v):Z(){__gmpz_set(&z,&v.z);}
 Z(Z&& v) noexcept:Z(){__gmpz_swap(&z,&v.z);}
 ~Z(){__gmpz_clear(&z);}
 Z& operator=(const Z& v){__gmpz_set(&z,&v.z);return *this;}
 Z& operator=(Z&& v) noexcept{__gmpz_swap(&z,&v.z);return *this;}
 Z& operator=(long v){__gmpz_set_si(&z,v);return *this;}
 Z& operator+=(const Z& v){__gmpz_add(&z,&z,&v.z);return *this;}
 Z& operator-=(const Z& v){__gmpz_sub(&z,&z,&v.z);return *this;}
 Z& operator*=(const Z& v){__gmpz_mul(&z,&z,&v.z);return *this;}
 Z& operator*=(long v){__gmpz_mul_si(&z,&z,v);return *this;}
 void add_scaled(const Z& v,long c){if(c>=0)__gmpz_addmul_ui(&z,&v.z,c);else __gmpz_submul_ui(&z,&v.z,-c);}
 bool operator==(long v)const{return __gmpz_cmp_si(&z,v)==0;}
 bool operator!=(long v)const{return __gmpz_cmp_si(&z,v)!=0;}
 bool operator<(long v)const{return __gmpz_cmp_si(&z,v)<0;}
 std::string str()const{char* p=__gmpz_get_str(nullptr,10,&z);std::string s(p);std::free(p);return s;}
};
inline Z operator+(const Z&a,const Z&b){Z c;__gmpz_add(&c.z,&a.z,&b.z);return c;}
inline Z operator-(const Z&a,const Z&b){Z c;__gmpz_sub(&c.z,&a.z,&b.z);return c;}
inline Z operator*(const Z&a,const Z&b){Z c;__gmpz_mul(&c.z,&a.z,&b.z);return c;}
inline Z operator*(const Z&a,long b){Z c;__gmpz_mul_si(&c.z,&a.z,b);return c;}
inline Z operator/(const Z&a,unsigned long b){Z c;__gmpz_tdiv_q_ui(&c.z,&a.z,b);return c;}
inline Z operator%(const Z&a,unsigned long b){Z c;__gmpz_tdiv_r_ui(&c.z,&a.z,b);return c;}
inline std::ostream& operator<<(std::ostream&o,const Z&a){return o<<a.str();}
inline long double approximate_ratio(const Z&a,const Z&b){long ea,eb;double ma=__gmpz_get_d_2exp(&ea,&a.z),mb=__gmpz_get_d_2exp(&eb,&b.z);return std::ldexp((long double)ma/mb,ea-eb);}
