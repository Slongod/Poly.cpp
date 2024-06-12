#include <bits/stdc++.h>

using namespace std;
namespace Poly
{
    const int _mod_ = 998244353 , _W_ = 23 , _N_ = (1<<_W_) + 37;

    struct poly {
        vector <int> f; int deg;
        void red(int d){deg = d; f.resize(d,0);}
        poly(int x = 1){red(x);}
        int& operator [] (int x){return f[x];}
        const int& operator [] (int x) const {assert(x < deg); return f[x];}
        void operator <<= (int x) {
            red(deg + x);
            for (int i = deg - 1; i >= x; i++){f[i] = f[i-x];}
            for (int i = 0; i < x; i++){f[i] = 0;}
        }
        void operator >>= (int x) {
            for (int i = 0; i + x < deg; i++){f[i] = f[i+x];} red(deg - x);
        }
        poly recut(int len){poly re = *this; re.red(len); return re;}
    };
    poly operator + (poly a , int x){a[0] = (1ll * a[0] + x + _mod_) % _mod_; return a;}
    poly operator + (int x , poly a){a[0] = (1ll * a[0] + x + _mod_) % _mod_; return a;}
    poly operator + (const poly &a , const poly &b) {
        poly re(max(a.deg , b.deg));
        for (int i = 0; i < re.deg; i++) {
            re[i] = (a[i] + b[i]) % _mod_;
        } return re;
    }
    poly operator - (const poly &a) {
        poly re = a;
        for (int i = 0; i < re.deg; i++) {
            re[i] = (_mod_ - re[i]) % _mod_;
        } return re;
    }
    poly operator - (const poly &a , const poly &b) {
        return a + (-b);
    }
    poly operator - (const poly &a , int y){return a + (-y);}
    poly operator - (int x , const poly &a){return x + (-a);}

    int _fw_[_W_] , _ifw_[_N_] , _invp_[_N_] , _dp_[_N_];
    inline int qkpow(int x , int y){int s; for(s=1;y;y/=2,x=1ll*x*x%_mod_){if(y&1){s=1ll*s*x%_mod_;}}return s;}
    inline void init()
    {
        _invp_[1] = 1;
        for (int i = 2; i < _N_; i++){_invp_[i] = 1ll * (_mod_ - 1) * (_mod_ / i) % _mod_ * _invp_[_mod_%i] % _mod_;}
        for (int i = 0; i < _W_; i++){_fw_[i] = qkpow(3 , (_mod_-1)/(1<<(i+1)));}
        for (int i = 0; i < _W_; i++){_ifw_[i] = qkpow(_fw_[i] , _mod_ - 2);}
    }
    inline void ntt(poly &f , int k , int opt)
    {
        for (int i = 1; i < (1 << k); i++){_dp_[i] = (_dp_[i>>1]>>1) | ((i&1)<<(k-1));}
        for (int i = 0; i < (1 << k); i++){if (i < _dp_[i]){swap(f[i] , f[_dp_[i]]);}}
        for (int i = 1 , ct = 0; i < (1 << k); i <<= 1 , ct++) {
            for (int j = 0 , w = opt == 1 ? _fw_[ct] : _ifw_[ct]; j < (1 << k); j += (i << 1)) {
                for (int l = 0 , now = 1; l < i; l++ , now = 1ll * now * w % _mod_) {
                    int x = f[l+j] , y = 1ll * f[l+j+i] * now % _mod_;
                    f[l+j] = (x + y) % _mod_; f[l+j+i] = (x - y + _mod_) % _mod_;
                }
            }
        }
        if (opt == -1) {
            int invn = qkpow((1 << k) , _mod_ - 2);
            for (int i = 0; i < (1 << k); i++) {
                f[i] = 1ll * f[i] * invn % _mod_;
            }
        }
    }
    
    //长度为 n 和长度为 m 的多项式相乘得到一个长度为 n+m-1 的多项式
    poly operator * (poly a , poly b)
    {
        int len = a.deg + b.deg - 1 , k = 0;
        while((1<<k) <= len){k++;} a.red(1<<k); b.red(1<<k);
        ntt(a , k , 1); ntt(b , k , 1); poly re(1<<k);
        for (int i = 0; i < (1 << k); i++){re[i] = 1ll * a[i] * b[i] % _mod_;}
        ntt(re , k , -1); re.red(len); return re;
    }
    poly operator * (poly a , int y){for (int i = 0; i < a.deg; i++){a[i] = 1ll * a[i] * y % _mod_;} return a;}
    poly operator * (int y , poly a){for (int i = 0; i < a.deg; i++){a[i] = 1ll * a[i] * y % _mod_;} return a;}
    //求出一个 g，令 fg=1(_mod_ x^f.deg)
    poly doinv(poly f , int k)
    {
        if (!k){poly re(1); re[0] = qkpow(f[0] , _mod_ - 2); return re;}
        poly g = doinv(f.recut(1<<k-1) , k - 1);
        g.red(1<<(k+1)); f.red(1<<(k+1));
        ntt(g , k+1 , 1); ntt(f , k+1 , 1);
        for (int i = 0; i < (1 << (k+1)); i++) {
            g[i] = (1ll * g[i] * (2 - 1ll * f[i] * g[i] % _mod_ + _mod_) % _mod_);
        } ntt(g , k+1 , -1); return g.recut(1<<k);
    }
    poly inv(poly f)
    {
        int k = 0 , dg = f.deg; while((1<<k) < dg){k++;}
        f.red(1<<k); return doinv(f , k).recut(dg);
    }
    //返回 f 的导数，长度为 f.deg-1
    poly der(const poly &f)
    {
        if (f.deg == 1){return poly();}
        poly re(f.deg - 1);
        for (int i = 1; i < f.deg; i++) {
            re[i-1] = 1ll * f[i] * i % _mod_;
        } return re;
    }
    //返回 f 的不定积分，长度为 f.deg+1
    poly integ(const poly &f)
    {
        poly re(f.deg + 1);
        for (int i = 0; i < f.deg; i++) {
            re[i+1] = 1ll * f[i] * _invp_[i+1] % _mod_;
        } return re;
    }
    //返回 g = ln(f) _mod_ x^f.deg
    poly ln(const poly &f){return integ(der(f) * inv(f)).recut(f.deg);}
    //返回 g = exp(f) _mod_ x^f.deg
    poly doexp(poly f , int k)
    {
        if (!k){poly re(1); re[0] = 1; return re;}
        poly g = doexp(f.recut((1<<(k-1))) , k-1);
        g.red(1<<k); return g * (1 + f - ln(g)).recut(1<<(k+1));
    }
    poly exp(poly f)
    {
        int dg = f.deg , k = 0; while((1<<k) < dg){k++;}
        f.red(1<<k); return doexp(f , k).recut(dg);
    }
    /*
    在使用前调用 init()
    */
    namespace Poly2D
    {
        struct poly2d {
            vector<poly> f; int degx , degy;
            void red(int dx , int dy) {
                degx = dx; degy = dy; f.resize(dx , poly(dy));
                for (int i = 0; i < dx; i++){f[i].red(dy);}
            }
            poly2d(){red(1 , 1);}
            poly2d(int dx , int dy){red(dx , dy);}
            poly& operator [] (int x){return f[x];}
            const poly& operator [] (int x) const {return f[x];}
            poly2d recut(int dx , int dy){poly2d re = *this; re.red(dx , dy); return re;}
            void nttx(int kx , int ky , int opt)
            {
                for (int i = 0; i < (1<<kx); i++) {
                    Poly::ntt(f[i] , ky , opt);
                }
            }
            void ntty(int kx , int ky , int opt)
            {
                poly t(1<<kx);
                for (int j = 0; j < (1<<ky); j++) {
                    for (int i = 0; i < (1<<kx); i++) {
                        t[i] = f[i][j];
                    } Poly::ntt(t , kx , opt);
                    for (int i = 0; i < (1<<kx); i++) {
                        f[i][j] = t[i];
                    }
                }
            }
            void ntt(int kx , int ky , int opt)
            {
                if (opt == 1){nttx(kx , ky , 1); ntty(kx , ky , 1);}
                else{ntty(kx , ky , -1); nttx(kx , ky , -1);}
            }
        };
        poly2d operator + (poly2d a , poly2d b)
        {
            int dx = max(a.degx , b.degx) , dy = max(a.degy , b.degy);
            a.red(dx , dy); b.red(dx , dy);
            for (int i = 0; i < dx; i++) {
                for (int j = 0; j < dy; j++) {
                    a[i][j] = (a[i][j] + b[i][j]) % _mod_;
                }
            } return a;
        }
        poly2d operator + (poly2d a , int x){a[0][0] = (a[0][0] + x) % _mod_; return a;}
        poly2d operator + (int x , poly2d a){a[0][0] = (a[0][0] + x) % _mod_; return a;}
        poly2d operator - (poly2d a)
        {
            for (int i = 0; i < a.degx; i++) {
                for (int j = 0; j < a.degy; j++) {
                    a[i][j] = (_mod_ - a[i][j]);
                }
            } return a;
        }
        poly2d operator - (const poly2d &a , const poly2d &b){return a + (-b);}
        poly2d operator - (const poly2d &a , int y){return a + (-y);}
        poly2d operator - (int x , const poly2d &a){return x + (-a);}

        poly2d operator * (poly2d a , int x)
        {
            for (int i = 0; i < a.degx; i++) {
                for (int j = 0; j < a.degy; j++) {
                    a[i][j] = 1ll * a[i][j] * x % _mod_;
                }
            } return a;
        }
        poly2d operator * (int x , poly2d a)
        {
            for (int i = 0; i < a.degx; i++) {
                for (int j = 0; j < a.degy; j++) {
                    a[i][j] = 1ll * a[i][j] * x % _mod_;
                }
            } return a;
        }
        poly2d operator * (poly2d a , poly2d b)
        {
            int dx = a.degx + b.degx - 1 , dy = a.degy + b.degy - 1;
            int kx = 0; while((1<<kx) <= dx){kx++;}
            int ky = 0; while((1<<ky) <= dy){ky++;}
            a.red(1<<kx , 1<<ky); b.red(1<<kx , 1<<ky);
            a.ntt(kx , ky , 1); b.ntt(kx , ky , 1);
            for (int i = 0; i < (1<<kx); i++) {
                for (int j = 0; j < (1<<ky); j++) {
                    a[i][j] = 1ll * a[i][j] * b[i][j] % _mod_;
                }
            } a.ntt(kx , ky , -1); a.red(dx , dy); return a;
        }
        //返回一个 fg=1 _mod_(x^f.degx , y^f.degy)
        poly2d doinv(poly2d f , int k)
        {
            if (!k){poly2d g; g[0] = inv(f[0]); return g;}
            poly2d g = doinv(f.recut(1<<(k-1) , f.degy) , k - 1);
            int dy = f.degy , tk = 0; while((1<<tk) < (dy<<2)){tk++;}
            g.red(1<<(k+1) , 1<<tk); f.red(1<<(k+1) , 1<<tk);
            g.ntt(k+1 , tk , 1); f.ntt(k+1 , tk , 1);
            for (int i = 0; i < (1<<(k+1)); i++) {
                for (int j = 0; j < (1<<tk); j++) {
                    g[i][j] = 1ll * g[i][j] * (2 - 1ll * f[i][j] * g[i][j] % _mod_ + _mod_) % _mod_;
                }
            } g.ntt(k+1 , tk , -1); return g.recut(1<<k , dy);
        }
        poly2d inv(poly2d f)
        {
            int k = 0 , dx = f.degx; while((1<<k) < dx){k++;}
            return doinv(f , k).recut(dx , f.degy);
        }

        //返回 f 对 x 求导，长度 f.deg-1
        poly2d der(const poly2d &f)
        {
            int dg = f.degx; poly2d g(dg-1 , f.degy);
            for (int i = 1; i < dg; i++) {
                g[i-1] = f[i] * i;
            } return g;
        }
        //返回 f 对 x 的不定积分，长度 f.deg+1
        poly2d integ(const poly2d &f)
        {
            int dg = f.degx; poly2d g(dg+1 , f.degy);
            for (int i = 0; i < dg; i++) {
                g[i+1] = f[i] * _invp_[i+1];
            } return g;
        }
        //返回 ln f，长宽与 f 相等
        poly2d ln(const poly2d &f)
        {
            poly2d re = integ(der(f) * inv(f)).recut(f.degx , f.degy);
            re[0] = Poly::ln(f[0]); return re;
        }
    }
}
using namespace Poly;
using namespace Poly2D;

int main()
{
    init();
}