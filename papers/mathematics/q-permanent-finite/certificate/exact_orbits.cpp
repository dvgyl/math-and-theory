#include "gmp_integer.hpp"
#include <array>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Row=std::array<long,3>;
using Poly=std::vector<Z>;
static size_t count(int d){return d<0?0:size_t(d+1)*(d+2)/2;}
static size_t index(int d,const std::array<int,3>&a){
    return size_t(a[0])*(d+1)-size_t(a[0])*(a[0]-1)/2+a[1];
}
template<class Fn>static void each(int d,Fn fn){
    size_t h=0;
    for(int i=0;i<=d;++i)for(int j=0;j<=d-i;++j)
        fn(h++,std::array<int,3>{i,j,d-i-j});
}
static Poly multiply(const Poly&f,int d,const Row&r){
    if(d<0)return {};
    const long a=r[0]*r[0],b=r[1]*r[1],c=r[2]*r[2];
    const std::array<std::array<int,3>,6> offsets={{{2,0,0},{0,2,0},{0,0,2},{1,1,0},{1,0,1},{0,1,1}}};
    const std::array<long,6> coefficients={{a*a,b*b,c*c,-2*a*b,-2*a*c,-2*b*c}};
    Poly out(count(d+2));
    each(d,[&](size_t h,const std::array<int,3>&alpha){
        if(f[h]==0)return;
        for(int t=0;t<6;++t)if(coefficients[t]){
            auto beta=alpha;
            for(int j=0;j<3;++j)beta[j]+=offsets[t][j];
            out[index(d+2,beta)].add_scaled(f[h],coefficients[t]);
        }
    });
    return out;
}
static Z norm(const Poly&f,int d,const Row&parity,const std::vector<Z>&facts){
    Z result=0;
    each(d,[&](size_t h,const std::array<int,3>&alpha){
        if(f[h]==0)return;
        Z weight=1;
        for(int j=0;j<3;++j)weight*=facts[2*alpha[j]+parity[j]];
        result+=f[h]*f[h]*weight;
    });
    return result;
}
int main(int argc,char**argv){
    try{
        if(argc<3)throw std::runtime_error("Usage: exact_orbits ORBITS.txt RESULT.json [COEFFICIENTS.json] [--average-only]");
        bool average_only=false;
        std::string coefficient_path;
        for(int i=3;i<argc;++i){
            if(std::string(argv[i])=="--average-only")average_only=true;
            else coefficient_path=argv[i];
        }
        std::ifstream input(argv[1]);
        int blocks=0;input>>blocks;
        if(!input||blocks<1||blocks>10000)throw std::runtime_error("Between 1 and 10000 orbit blocks required");
        std::string line;std::getline(input,line);
        std::vector<Row> rows;
        std::vector<long> correction_weights;
        for(int block=0;block<blocks;++block){
            if(!std::getline(input,line))throw std::runtime_error("Missing orbit input");
            if(line.empty()){--block;continue;}
            std::istringstream parser(line);Row r;long copies=1;
            parser>>r[0]>>r[1]>>r[2];
            if(!parser)throw std::runtime_error("Invalid orbit coordinates");
            long optional;if(parser>>optional)copies=optional;
            if(copies<1||copies>10000||rows.size()+copies>10000)throw std::runtime_error("Invalid total orbit multiplicity");
            for(long j=0;j<copies;++j){rows.push_back(r);correction_weights.push_back(2*j+1);}
        }
        const int m=rows.size();
        // This bound keeps all signed-long coefficient multipliers safe.
        for(const auto&r:rows){
            if(r[0]==0&&r[1]==0&&r[2]==0)throw std::runtime_error("Zero row type");
            for(long v:r)if(v<0||v>1000)throw std::runtime_error("Coordinates must lie in [0,1000]");
        }
        const auto start=std::chrono::steady_clock::now();
        Poly f(1);f[0]=1;
        std::array<Poly,5> u;
        for(int old=0;old<m;++old){
            const auto&r=rows[old];
            const long a=r[0]*r[0],b=r[1]*r[1],c=r[2]*r[2];
            const long scale=8*r[0]*r[2];
            const int d=2*old;
            Poly nf=multiply(f,d,r);
            std::array<Poly,5> nu;
            for(int t=0;t<(average_only?3:5);++t){
                const int degree=d-((t==1||t==4)?1:2);
                if(old)nu[t]=multiply(u[t],degree,r);
                else nu[t].resize(count(d+((t==1||t==4)?1:0)));
            }
            each(d,[&](size_t h,const std::array<int,3>&alpha){
                if(f[h]==0)return;
                const long i=alpha[0],j=alpha[1],k=alpha[2];
                nu[0][h].add_scaled(f[h],scale*b*(1+2*i+j));
                nu[2][h].add_scaled(f[h],-scale*b*(1+j+2*k));
                if(j){
                    auto beta=alpha;--beta[1];++beta[0];
                    const size_t dest=index(d,beta);
                    nu[0][dest].add_scaled(f[h],scale*a*j);
                    nu[2][dest].add_scaled(f[h],scale*a*j);
                    beta=alpha;--beta[1];++beta[2];
                    const size_t dest2=index(d,beta);
                    nu[0][dest2].add_scaled(f[h],-scale*c*j);
                    nu[2][dest2].add_scaled(f[h],-scale*c*j);
                }
                const std::array<long,3> sources={{scale*a*(1+i+k),scale*b*(k-i),-scale*c*(1+i+k)}};
                for(int q=0;q<3;++q)if(sources[q]){
                    auto beta=alpha;++beta[q];
                    nu[1][index(d+1,beta)].add_scaled(f[h],sources[q]);
                }
                if(!average_only){
                    const long correction=correction_weights[old];
                    nu[3][h].add_scaled(f[h],correction*8*a*r[1]*r[2]);
                    const std::array<long,3> extra={{correction*4*r[1]*r[2]*a,-correction*4*r[1]*r[2]*b,correction*4*r[1]*r[2]*c}};
                    for(int q=0;q<3;++q)if(extra[q]){
                        auto beta=alpha;++beta[q];
                        nu[4][index(d+1,beta)].add_scaled(f[h],extra[q]);
                    }
                }
            });
            f.swap(nf);u.swap(nu);
            if((old+1)%16==0||old+1==m)
                std::cerr<<"orbits="<<old+1<<" order="<<4*(old+1)<<" monomials="<<f.size()
                         <<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";
        }
        const int n=4*m;
        std::vector<Z> facts(n+1);facts[0]=1;
        for(int j=1;j<=n;++j)facts[j]=facts[j-1]*j;
        const std::array<Row,5> parity={{{0,1,1},{0,0,0},{1,1,0},{1,0,1},{0,0,0}}};
        Z permanent=norm(f,2*m,{0,0,0},facts),wedge=0,average=0;
        std::array<Z,5> component;
        for(int t=0;t<(average_only?3:5);++t){
            const int degree=2*m-((t==1||t==4)?1:2);
            component[t]=norm(u[t],degree,parity[t],facts);
            wedge+=component[t];
            if(t<3)average+=component[t];
        }
        Z denominator=permanent*n*(n-1)/2;
        Z twice_derivative=denominator-wedge;
        if(!average_only&&twice_derivative%2!=0)throw std::runtime_error("Actual derivative parity check failed");
        const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        std::ofstream out(argv[2]);if(!out)throw std::runtime_error("Cannot open result output");
        out<<"{\n  \"scope\": \"Exact D2-orbit recurrence in squared coordinates\",\n"
           <<"  \"orbit_block_count\": "<<blocks<<",\n  \"orbit_count\": "<<m<<",\n  \"order\": "<<n<<",\n"
           <<"  \"actual_wedge_included\": "<<(average_only?"false":"true")<<",\n"
           <<"  \"permanent\": \""<<permanent<<"\",\n"
           <<"  \"averaged_wedge_norm_squared\": \""<<average<<"\",\n"
           <<"  \"wedge_norm_squared\": \""<<wedge<<"\",\n"
           <<"  \"twice_derivative_upper_bound\": \""<<twice_derivative<<"\",\n"
           <<"  \"negative_derivative_certified\": "<<(twice_derivative<0?"true":"false")<<",\n"
           <<"  \"average_alone_certifies_negative\": "<<((denominator-average)<0?"true":"false")<<",\n"
           <<"  \"wedge_ratio_decimal\": \""<<std::setprecision(17)<<approximate_ratio(wedge,denominator)<<"\",\n"
           <<"  \"average_ratio_decimal\": \""<<std::setprecision(17)<<approximate_ratio(average,denominator)<<"\",\n"
           <<"  \"parity_component_norms\": [";
        for(int t=0;t<(average_only?3:5);++t)out<<(t?", ":"")<<'"'<<component[t]<<'"';
        out<<"],\n  \"seconds\": "<<seconds<<"\n}\n";
        if(!coefficient_path.empty()){
            std::ofstream cf(coefficient_path);if(!cf)throw std::runtime_error("Cannot open coefficient output");
            const std::array<std::string,6> names={{"F","U01","U02","U12","V01","V12"}};
            cf<<"{\n  \"monomial_order\": \"increasing exponent of X, then increasing exponent of Y; Z is remaining degree\",\n  \"polynomials\": [\n";
            for(int t=-1;t<(average_only?3:5);++t){
                const Poly&poly=t<0?f:u[t];
                const int degree=t<0?2*m:2*m-((t==1||t==4)?1:2);
                cf<<(t>=0?",\n":"")<<"    {\"name\": \""<<names[t+1]<<"\", \"degree\": "<<degree<<", \"coefficients\": [";
                for(size_t h=0;h<poly.size();++h)cf<<(h?", ":"")<<'"'<<poly[h]<<'"';
                cf<<"]}";
            }
            cf<<"\n  ]\n}\n";
        }
        std::cerr<<"EXACT negative certificate="<<(twice_derivative<0?"yes":"no")
                 <<" ratio="<<std::setprecision(17)<<approximate_ratio(wedge,denominator)<<" seconds="<<seconds<<"\n";
        return 0;
    }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}
}
