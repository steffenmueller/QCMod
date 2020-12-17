matrix2vector:=function(M);
d:=NumberOfRows(M);
v:=Vector(Parent(M[1,1]),d^2,[0:i in [1..d^2]]);
k:=0;
for i in [1..d] do
    for j in [1..d] do
        k:=k+1;
        v[k]:=M[j,i];
    end for;
end for;
return v;
end function;

vector2matrix:=function(v);
print NumberOfColumns(v);
d:=Integers()!SquareRoot(NumberOfColumns(v));
M:=ZeroMatrix(Parent(v[1]),d,d);
k:=0;
for i in [1..d] do
    for j in [1..d] do
        k:=k+1;
        M[j,i]:=v[k];
    end for;
end for;
return M;
end function;

vector2matrixalt:=function(v,d);
print NumberOfColumns(v);
M:=ZeroMatrix(Parent(v[1]),d,d);
k:=0;
for i in [1..d] do
    for j in [1..i-1] do
        k:=k+1;
        M[j,i]:=v[k];
        M[i,j]:=-v[k];
    end for;
end for;
return M;
end function;

matrix2matrix:=function(M);
d:=NumberOfRows(M);
e:=ExactQuotient(d*(d-1),2);
N:=ZeroMatrix(Parent(M[1,1]),e,e);
n:=0;
for i in [1..d] do
    for j in [1..i-1] do
        n:=n+1;
        E:=ZeroMatrix(Parent(M[1,1]),d,d);
        E[i,j]:=1;
        E[j,i]:=-1;
        J:=M*E*Transpose(M);
        m:=0;
        for k in [1..d] do
            for l in [1..k-1] do
                m:=m+1;
                N[n,m]:=J[k,l];
            end for;
        end for;
    end for;
end for;
return N;
end function;

findZ:=function(F,p,N);
prec:=N;
E:=matrix2matrix(F);
print E;
d:=NumberOfRows(C);
d2:=ExactQuotient(d,2);
C:=ZeroMatrix(Parent(F[1,1]),d,d);
for i in [1..d2] do
C[i+d2,i]:=1;
C[i,i+d2]:=-1;
end for;
e:=NumberOfRows(E);
Rp<xp>:=PolynomialRing(pAdicField(p,prec));
Ro<xo>:=PolynomialRing(Rationals());
M:=ChangeRing(ChangeRing(ChangeRing(ChangeRing(E-p,Integers()),IntegerRing(p^prec)),Integers()),Rationals());
W:=[vector2matrixalt(b,d):b in Basis(Kernel(ChangeRing(M,pAdicField(p,prec-2))))];
W:=[ChangeRing(w,Rationals()):w in W];
c:=[&+[&+[C[i,j]*W[k][i,j]:j in [1..d]]:i in [1..d]]:k in [1..#W]];
M:=[c[#W]*W[i]-c[i]*W[#W]:i in [1..#W-1]];
      Wo:=ZeroMatrix(Rationals(),d,d);
      Wo[1,d2+1]:=1;
      Wo[d2+1,1]:=-1;
Mo:=[Matrix(Rationals(),d,d,[[lindepQp(pAdicField(p,prec)!m[j,i]):i in [1..d]]:j in [1..d]]):m in M];
Mo:=[2*m+Trace(m*C)*Wo:m in M];
return Mo;
end function;
//chiQ:=CharacteristicPolynomial(E-p);
//chi:=PolynomialRing(pAdicField(p,prec))!chiQ;
//chi2:=ExactQuotient(chi,xp^NumberOfRows(E));

