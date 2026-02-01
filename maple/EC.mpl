with(LinearAlgebra):
with(combinat):

svp := proc(f,v)   
# Sign Variation of Polynomial
# In : f, a polynomial in v with real coeffcients
#      v, a variable
# Out: the sign variataion count of the coefficients of f
  local d,L,Lb, Cb, i,c;
  d  := degree(f,v);
  L  := [coeff(f,v,d-i)$i=0..d];
  return svl(L);
end:


svl := proc(L)    
# Sign Variation of List
# In : L, a list of real numbers
# Out: the sign variation count on L
  local Lb, Cb, i, c,v;
  Lb := remove(v->evalf(v=0), L);
  Cb := [seq(Lb[i]*Lb[i+1],i=1..nops(Lb)-1)];
  Cb := remove(v->evalf(v>0), Cb);
  c  := nops(Cb);
  return c;
end:  


cpl := proc(Ls)    
# Cartesian Product of Lists
# In : Ls, a list of lists
# Out: The cartesian product of Ls
  local P,p,C;
  P := cartprod(Ls);
  C := [];
  while not P[finished] do
    C := [op(C), P[nextvalue]()];
  end do;
  
  # C := [seq(Reverse(convert(p[],list)),p=P)];
  return C;
end:


kpm := proc(Ms)    
# Kroneker Product of Matrices
# In : Ms, a list of matrices
# Out: The Kronecker products of Ms
  return foldl(KroneckerProduct,op(Ms));
end:


kpl := proc(Ls)    
# Kronecker Product of Lists
# In : Ls, a list of lists
# Out: The Kronecker products of Ls
  local Ms,L;
  Ms := map(L-><op(L)>,Ls);
  return map(expand,convert(kpm(Ms),list));
end:


sig := proc(M)      
# Signature of Matrix 
# In : M, a real symmetric matrix
# Out: the signature (difference between number of positive and negative eigenvalues) of M
  local cp,n,s;
  n  := RowDimension(M);
  cp := CharacteristicPolynomial(M,lambda);
  s  := 2*svp(cp,lambda) - n + ldegree(cp,lambda);
  return s;
end:


epm := proc(f,v,M)   
# Evaluate Polynomial on Matrix
# In : f, a polynomial in v
#      v, a variable
#      M, a matrix
# Out: f(M)
  local F,fe,k;
  fe := expand(f);
  F  := simplify(coeff(fe,v,0)*IdentityMatrix(RowDimension(M)) + add(coeff(fe,v,k)*M^k,k=1..degree(fe)));
  return F;
end:

esvp := proc(f,v)   
# Extended Sign Variation of Polynomial
# In : f, a polynomial in v with real coefficients
#      v, a variable
# Out: the sign variataion count on the coefficients of f
  local d,L,Lb, Cb, i,c;
  d  := degree(f,v);
  L  := [coeff(f,v,d-i)$i=0..d];
  c  := esvl(L);
  return c;
end:

esvl := proc(L)  
# Extended Sign Variation of List
# In : L, a list of real numbers
# Out: extended sign variation count on L
  local inds,es,svcs,Le,c;
  inds := [SearchAll(0, L)];
  es := cpl([[-1,1]$nops(inds)]);
  svcs := 0;
  for e in es do
    Le := L;
    for i from 1 to nops(inds) do
      Le[inds[i]] := e[i];
    od:
    svcs := svcs + svl(Le);
  od:
  
  c := 1/nops(es) * svcs;
  return c; 
end:

Vbar := proc(m)      
# Extended V matrix
# In :  m, an positive integer
# Out:  Vbar, m by 3^m Vbar matrix
  local Vb;
  Vb  := cpl([[-1,0,1]$m]);
  Vb  := map(v->svl([op(v),1]),Vb);
  Vb  := Matrix(m,3^m,(t,s)->`if`(Vb[s]=m-t,1,0));
  return Vb;
end:

V := proc(m)      
# V matrix
# In :  m, positive integer
# Out:  V, m by 2^m V matrix
  local Vm;
  Vm  := cpl([[-1,1]$m]);
  Vm  := map(v->svl([op(v),1]),Vm);
  Vm  := Matrix(m,2^m,(t,s)->`if`(Vm[s]=m-t,1,0));
  return Vm;
end:

Hbar := proc(m)     
# Hbar matrix
# In : m, positive integer
# Out: H, a 3^m by 3^m H matrix
  return kpm([Matrix(3,3,[[1,1,1],[-1,0,1],[1,0,1]])$m]);
end:

H := proc(m)     
# H matrix
# In : m, positive integer
# Out: H, a 2^m by 2^m H matrix
  return kpm([Matrix(2,2,[[1,1],[-1,1]])$m]);
end:

Csig := proc(m)   
# Combinatorial part for signature method
# In : m, positive integer
# Out: Csig
  return V(m) . H(m)^(-1);
end:

ECsig3 := proc(F,G)    
# Eigenvalue Configuration using 3x3 H matrix
# In : F, G, numeric real symmetric matrices
# Out: Eigenvalue configuration of F and G   
  local m,n,f,fp,es,fes,feGs,hes,sves,tdes,sigma,Hb,Vb,c,i,fe,feG,he,e,q,r;
  m     := RowDimension(F);
  n     := RowDimension(G);  
  f     := CharacteristicPolynomial(F,x);
  fp    := [seq(diff(f,[x$i]),i=0..m-1)];
  es    := cpl([[0,1,2]$m]);
  fes   := [seq(mul(fp[i+1]^e[i+1],i=0..m-1),e=es)];
  feGs  := [seq(epm(fe,x,G),fe=fes)];
  hes   := [seq(CharacteristicPolynomial(feG,x),feG=feGs)];
  sves  := [seq(svp(he,x),he=hes)];
  tdes  := [seq(ldegree(he,x),he=hes)];
  sigma := [seq(2*sves[i]-n+tdes[i],i=1..nops(sves))];
  sigma := Vector(sigma);
  Hb    := Hbar(m);
  Vb    := Vbar(m);
  r     := Hb^(-1).sigma;
  c     := Vb.r;
  return c;
end:

ECsig := proc(F,G)    
# Eigenvalue Configuration. signature method
# In : F, G, numeric real symmetric matrices
# Out: Eigenvalue configuration of F and G   
  local m,n,f,fp,es,fes,i,feGs,hes,sigma,Vm,Hm,c,e,fe,feG,sves,he,tdes,q,r;
  m     := RowDimension(F);
  n     := RowDimension(G);  
  f     := CharacteristicPolynomial(F,x);
  fp    := [seq(diff(f,[x$i]),i=0..m-1)];
  es    := cpl([[0,1]$m]);
  fes   := [seq(mul(fp[i+1]^e[i+1],i=0..m-1),e=es)];
  feGs  := [seq(epm(fe,x,G),fe=fes)];
  hes   := [seq(CharacteristicPolynomial(feG,x),feG=feGs)];
  sves  := [seq(svp(he,x),he=hes)];
  tdes  := [seq(ldegree(he,x),he=hes)];
  sigma := [seq(2*sves[i]-n+tdes[i],i=1..nops(sves))];
  sigma := Vector(sigma);
  Hm    := H(m);
  Vm    := V(m);
  r     := Hm^(-1).sigma;
  c     := Vm.r;
  return c;
end:

Asig := proc(F,G)   
# Algebraic part for the signature method
# In : F, G symbolic real symmetric matrices
# Out: Asig(F,G)
  local m,n,f,g,fp,i,es,fes,e,feGs,fe,hes,feG;
  m := RowDimension(F);
  n := RowDimension(G);
  #F := Matrix(m,m,(i,j)->a[i,j], shape=symmetric);
  #G := Matrix(n,n,(i,j)->b[i,j], shape=symmetric);
  f := CharacteristicPolynomial(F, x);
  g := CharacteristicPolynomial(G, x);
  
  fp := [seq(diff(f,[x$i]),i=0..m-1)];
  es    := cpl([[0,1]$m]);
  fes   := [seq(mul(fp[i+1]^e[i+1],i=0..m-1),e=es)];
  feGs  := [seq(epm(fe,x,G),fe=fes)];
  hes   := [seq(CharacteristicPolynomial(feG,x),feG=feGs)];
  return Vector(hes);
end:

ConditionsSig := proc(F,G)   
# Conditions for EC, signature method
# In : F, G, symbolic real symmetric matrices
# Out: Csig, Asig such that c = EC(F,G) iff c = Csig . sig(Asig)
  return Csig(RowDimension(F)), Asig(F,G);
end:

ESP := proc(k, X)
# Elementary Symmetric Polynomial
# In  : k, integer between 1 and n
#       X, list of variables
# Out : the kth symmetric polynomial in X
  local s,x;
  
  return add(mul(x, x in s), s in choose(X, k)):
end:

FTSP := proc(h, X, ov)
# Fundamental Theorem of Symmetric Polynomials
# In  : h, symmetric polynomial in X
#     : X, list of variables
#     : ov, output variable
# Out : p, polynomial in ov[1],...,ov[n] such that h = p(s(1,n), ..., s(n, n)), 
#          where s(k, n) are the elementary symmetric polynomials on X
  local n, hs, ps, g, i, d, w, p;

  n := nops(X);
  
  # base case: n = 1 or totaldegree(h) = 0
  if n = 1 or degree(h, {op(X)}) <= 0 then
    return eval(h, [seq(X[i] = ov[i], i=1..n)]);
  fi;
  
  hs := eval(h, X[n] = 0);
  ps := FTSP(hs, X[1..n-1], ov);
  g := eval(ps, [seq(ov[i] = ESP(i, X), i=1..n-1)]);
  d := expand((h - g)/ESP(n, X));
  w := FTSP(d, X, ov);
  p := w * ov[n] + ps;
  return expand(p);
end:

TM := proc(m)
# T Matrix
# In : m, positive integer
# Out: T, T matrix
  local Tm,i,j,t,k,r,iss,is;
  Tm := Matrix(m,m);
  for k from 1 to m do
    iss := choose(m,k);
    for r from 1 to m do
      t := 0;
      for is in iss do
        if irem(nops(select(e->e<=r,is)),2)=1 then
          t := t + 1; 
        fi;
      od;
      Tm[k,r] := t;
    od;
  od;
  return Tm;
end:

Csym := proc(m)
# Combinatorial part, symmetry method
# In : m, positive integer
# Out: Csym
  return TM(m)^(-1);
end:

hv := proc(m,n,r)
# h Polynomial
# In : m, n, r, positive integers
# Out: hr, the r-th h polynomial
  local hr,iss,is,i,j,w;
  hr := 1;
  iss := choose(m,r);
  for j from 1 to n do
    for is in iss do
      w := mul(alpha[i]-beta[j],i=is);
      hr := hr*(x+w);
    od;
  od;
  return hr;
end:

Asym := proc(F,G)
# Algebraic part, symmetric polynomial method
# In : F, G, symbolic real symmetric matrices
# Out: Asym, a vector of polynomials
  local m,n,f,g,As,r,p,h,i;
  m := RowDimension(F);
  n := RowDimension(G);
  f := CharacteristicPolynomial(F, x);
  g := CharacteristicPolynomial(G, x);

  As := [];
  for r from 1 to m do
    h := hv(m, n, r);
    p := FTSP(h, [seq(beta[i],   i=1..n)], y);
    p := FTSP(p, [seq(alpha[i],  i=1..m)], z);
    p := eval(p, [seq(y[i]=coeff(g,x,n-i) * (-1)^i, i=1..n)]);
    p := eval(p, [seq(z[i]=coeff(f,x,m-i) * (-1)^i, i=1..m)]);
    As := [op(As), collect(p,x)];
  od:

  return Vector(As);
end:

ECsym := proc(F,G)    
# Eigenvalue Configuration, symmetric polynomial method
# In : F, G, numeric real symmetric matrices
# Out: Eigenvalue configuration of F and G   
  local m,Tm,Dsc,vd,d,c;
  m   := RowDimension(F);
  Tm  := TM(m);
  Dsc := Dsym(F,G);
  vd  := Vector([seq(esvp(d,x), d in Dsc)]);
  c   := Tm^(-1) . vd;
  return c;
end:

ConditionsSym := proc(F,G)
# Conditions for EC, symmetric polynomial method
# In : F, G, symbolic real symmetric matrices
# Out: Csym, Asym such that c = EC(F,G) iff c = Csym . v(Asym)
  return Csym(RowDimension(F)), Asym(F,G);
end:
