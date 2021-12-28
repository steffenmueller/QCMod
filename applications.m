function are_equal_records(P, Q)
  return &and[IsWeaklyEqual(P`x, Q`x), P`inf eq Q`inf,
            &and[IsWeaklyEqual(P`b[i], Q`b[i]) : i in [1..#P`b]]];
end function;

function is_teichmueller(P, data)
  Q := teichmueller_pt(P, data);
  return are_equal_records(P, Q);
end function;



Fp_points:=function(data);

  // Finds all points on the reduction mod p of the curve given by data

  Q:=data`Q; p:=data`p; d:=Degree(Q);  W0:=data`W0; Winf:=data`Winf; 

  Fp:=FiniteField(p); Fpx:=RationalFunctionField(Fp); Fpxy:=PolynomialRing(Fpx);
  f:=Fpxy!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+(Fp!Coefficient(Coefficient(Q,i),j))*Fpxy.1^i*Fpx.1^j;
    end for;
  end for;  
  FFp:=FunctionField(f); // function field of curve mod p

  places:=Places(FFp,1);

  b0modp:=[]; // elements of b^0 mod p
  for i:=1 to d do
    f:=FFp!0;
    for j:=1 to d do
      f:=f+(Fpx!W0[i,j])*FFp.1^(j-1);
    end for;
    b0modp[i]:=f;
  end for;

  binfmodp:=[]; // elements of b^inf mod p
  for i:=1 to d do
    f:=FFp!0;
    for j:=1 to d do
      f:=f+(Fpx!Winf[i,j])*FFp.1^(j-1);
    end for;
    binfmodp[i]:=f;
  end for;

  Fppts:=[];
  for i:=1 to #places do
    if Valuation(FFp!Fpx.1,places[i]) ge 0 then
      if Valuation(FFp!Fpx.1-Evaluate(FFp!Fpx.1,places[i]),places[i]) eq 1 then
        index:=0;
      else
        j:=1;
        done:=false;
        while not done and j le d do
          if Valuation(b0modp[j]-Evaluate(b0modp[j],places[i]),places[i]) eq 1 then
            done:=true;
            index:=j;
          end if;
          j:=j+1;
        end while;
      end if;
      Fppts:=Append(Fppts,[*Evaluate(FFp!Fpx.1,places[i]),[Fp!Evaluate(b0modp[j],places[i]): j in [1..d]],false,index*]);    
    else
      if Valuation(FFp!(1/Fpx.1)-Evaluate(FFp!(1/Fpx.1),places[i]),places[i]) eq 1 then
        index:=0;
      else
        j:=1;
        done:=false;
        while not done and j le d do
          if Valuation(binfmodp[j]-Evaluate(binfmodp[j],places[i]),places[i]) eq 1 then
            done:=true;
            index:=j;
          end if;
          j:=j+1;
        end while;
      end if;
      Fppts:=Append(Fppts,[*Evaluate(FFp!(1/Fpx.1),places[i]),[Fp!Evaluate(binfmodp[j],places[i]): j in [1..d]],true,index*]);
    end if;
  end for;

  return Fppts;

end function;


Qp_points:=function(data:points:=[], Nfactor:=1.5);

  // For every point on the reduction mod p of the curve given by data,
  // a Qp point on the curve is returned that reduces to it. Optionally,
  // an (incomplete) list of points can be specified by the user which will
  // then be completed.
  
  Q:=data`Q; p:=data`p; N:=data`N; r:=data`r; W0:=data`W0; Winf:=data`Winf; 
  d:=Degree(Q); Fp:=FiniteField(p); 
  Qx:=RationalFunctionField(RationalField()); Qxy:=PolynomialRing(Qx);

  Nwork:=Ceiling(N*Nfactor); // Look at this again, how much precision loss in Roots()?
  Qp:=pAdicField(p,Nwork); Qpy:=PolynomialRing(Qp); Zp:=pAdicRing(p,Nwork); Zpy:=PolynomialRing(Zp);
  
  Fppts:=Fp_points(data);
  Qppts:=[];

  f:=Qxy!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qxy.1^i*Qx.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  b0fun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W0[i,j]*FF.1^(j-1);
    end for;
    b0fun[i]:=bi;
  end for;

  binffun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+Winf[i,j]*FF.1^(j-1);
    end for;
    binffun[i]:=bi;
  end for;

  for i:=1 to #Fppts do

    Fppoint:=Fppts[i];
    j:=1;
    done:=false;
    while not done and j le #points do
      if (Fppoint[3] eq points[j]`inf) and (Fp!(points[j]`x)-Fppoint[1] eq 0) and ([Fp!(points[j]`b)[k]:k in [1..d]] eq Fppoint[2]) then
        done:=true;
        P:=points[j];
      end if;
      j:=j+1; 
    end while;
    
    if not done then
      
      if Fppoint[3] then // infinite point
        
        inf:=true;
        
        if Fppoint[4] eq 0 then // x - point[1] local coordinate
          x:=Qp!Fppoint[1];
          b:=[];
          for j:=1 to d do
            bj:=binffun[j];

            if not assigned data`minpolys or data`minpolys[2][1,j+1] eq 0 then
              data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
            end if;
            poly:=data`minpolys[2][1,j+1];

            C:=Coefficients(poly);
            D:=[];
            for k:=1 to #C do
              D[k]:=Evaluate(C[k],x); 
            end for;
            fy:=Qpy!Zpy!D;
            fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
            zeros:=[];
            for j:=1 to #fac do
              if Degree(fac[j][1]) eq 1 then
                zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
              end if;
            end for;

            done:=false;
            k:=1;
            while not done and k le #zeros do
              if (Fp!zeros[k]-Fppoint[2][j] eq 0) then 
                done:=true;
                b[j]:=zeros[k];
              end if;
              k:=k+1;
            end while;
          end for;
        else // x-point[1] not local coordinate
          index:=Fppoint[4];
          bindex:=Qp!Fppoint[2][index];

          if not assigned data`minpolys or data`minpolys[2][index+1,1] eq 0 then
            data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
          end if;
          poly:=data`minpolys[2][index+1,1];

          C:=Coefficients(poly);
          D:=[];
          for k:=1 to #C do
            D[k]:=Evaluate(C[k],bindex); 
          end for;
          fy:=Qpy!Zpy!D;
          fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
          zeros:=[];
          for j:=1 to #fac do
            if Degree(fac[j][1]) eq 1 then
              zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
            end if;
          end for;

          done:=false;
          k:=1;
          while not done and k le #zeros do
            if (Fp!zeros[k]-Fppoint[1] eq 0) then 
              done:=true;
              x:=zeros[k];
            end if;
            k:=k+1;
          end while;
          b:=[];
          for j:=1 to d do
            if j eq index then
              b[j]:=bindex;
            else

              if not assigned data`minpolys or data`minpolys[2][index+1,j+1] eq 0 then
                data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
              end if;
              poly:=data`minpolys[2][index+1,j+1];

              C:=Coefficients(poly);
              D:=[];
              for k:=1 to #C do
                D[k]:=Evaluate(C[k],bindex); 
              end for;
              fy:=Qpy!Zpy!D;
              fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
              zeros:=[];
              for j:=1 to #fac do
                if Degree(fac[j][1]) eq 1 then
                  zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
                end if;
              end for;

              done:=false;
              k:=1;
              while not done and k le #zeros do
                if (Fp!zeros[k]-Fppoint[2][j] eq 0) then 
                  done:=true;
                  b[j]:=zeros[k];
                end if;
                k:=k+1;
              end while;
            end if;
          end for; 
        end if;

      else // finite point
        inf:=false;
        if Fppoint[4] eq 0 then // x - point[1] local coordinate

          x:=Qp!Fppoint[1];

          if Valuation(Evaluate(r,x)) eq 0 then // good point
            W0invx:=Transpose(Evaluate(W0^(-1),x));
            ypowersmodp:=Vector(Fppoint[2])*ChangeRing(W0invx,FiniteField(p));
            y:=Qp!ypowersmodp[2];

            C:=Coefficients(Q);
            D:=[];
            for i:=1 to #C do
              D[i]:=Evaluate(C[i],x);
            end for;
            fy:=Qpy!Zpy!D;

            y:=HenselLift(fy,y); // Hensel lifting
            ypowers:=[];
            ypowers[1]:=Qp!1;
            for i:=2 to d do
              ypowers[i]:=ypowers[i-1]*y;
            end for;
            ypowers:=Vector(ypowers);

            W0x:=Transpose(Evaluate(W0,x));
            b:=Eltseq(ypowers*ChangeRing(W0x,Parent(ypowers[1])));
          else // bad point
            for j:=1 to d do
              bj:=b0fun[j];

              if not assigned data`minpolys or data`minpolys[1][1,j+1] eq 0 then
                data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
              end if;
              poly:=data`minpolys[1][1,j+1];

              C:=Coefficients(poly);
              D:=[];
              for k:=1 to #C do
                D[k]:=Evaluate(C[k],x); 
              end for;
              fy:=Qpy!Zpy!D;
              fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
              zeros:=[];
              for j:=1 to #fac do
                if Degree(fac[j][1]) eq 1 then
                  zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
                end if;
              end for;

              done:=false;
              k:=1;
              while not done and k le #zeros do
                if (Fp!zeros[k]-Fppoint[2][j] eq 0) then 
                  done:=true;
                  b[j]:=zeros[k];
                end if;
                k:=k+1;
              end while;
            end for;
          end if;

        else // x-point[1] not local coordinate
          index:=Fppoint[4];
          bindex:=Qp!Fppoint[2][index];

          if not assigned data`minpolys or data`minpolys[1][index+1,1] eq 0 then
            data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
          end if;
          poly:=data`minpolys[1][index+1,1];

          C:=Coefficients(poly);
          D:=[];
          for k:=1 to #C do
            D[k]:=Evaluate(C[k],bindex); 
          end for;
          fy:=Qpy!Zpy!D;
          fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
          zeros:=[];
          for j:=1 to #fac do
            if Degree(fac[j][1]) eq 1 then
              zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
            end if;
          end for;

          done:=false;
          k:=1;
          while not done and k le #zeros do
            if (Fp!zeros[k]-Fppoint[1] eq 0) then 
              done:=true;
              x:=zeros[k];
            end if;
            k:=k+1;
          end while;
          b:=[];
          for j:=1 to d do
            if j eq index then
              b[j]:=bindex;
            else

              if not assigned data`minpolys or data`minpolys[1][index+1,j+1] eq 0 then
                data:=update_minpolys(data,Fppoint[3],Fppoint[4]);
              end if;
              poly:=data`minpolys[1][index+1,j+1];

              C:=Coefficients(poly);
              D:=[];
              for k:=1 to #C do
                D[k]:=Evaluate(C[k],bindex); 
              end for;
              fy:=Qpy!Zpy!D;
              fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
              zeros:=[];
              for j:=1 to #fac do
                if Degree(fac[j][1]) eq 1 then
                  zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
                end if;
              end for;

              done:=false;
              k:=1;
              while not done and k le #zeros do
                if (Fp!zeros[k]-Fppoint[2][j] eq 0) then 
                  done:=true;
                  b[j]:=zeros[k];
                end if;
                k:=k+1;
              end while;
            end if;
          end for;
        end if;
        
      end if;

      P:=set_bad_point(x,b,inf,data);

    end if;

    if is_bad(P,data) and not is_very_bad(P,data) then
      P:=find_bad_point_in_disk(P,data);
    end if;
    
    Qppts:=Append(Qppts,P);
  
  end for;

  return Qppts,data;

end function;


Q_points:=function(data,bound);

  // Returns a list (not guaranteed to be complete) of Q-rational points 
  // upto height bound on the curve given by data.

  Q:=data`Q; p:=data`p; N:=data`N; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q);

  pointlist:=[];

  A2:=AffineSpace(RationalField(),2);
  Qxy:=PolynomialRing(RationalField(),2);
  
  QA2:=Qxy!0;
  C:=Coefficients(Q);
  for i:=1 to #C do
    D:=Coefficients(C[i]);
    for j:=1 to #D do
      QA2:=QA2+D[j]*(Qxy.1)^(j-1)*(Qxy.2)^(i-1);
    end for;
  end for;
  
  X:=Scheme(A2,QA2);
  pts:=PointSearch(X,bound);
  xvalues:=[];
  for i:=1 to #pts do
    if not pts[i][1] in xvalues then
      xvalues:=Append(xvalues,pts[i][1]);
    end if;
  end for;

  Qx:=RationalFunctionField(RationalField());
  Qxy:=PolynomialRing(Qx);
  Qfun:=Qxy!0;
  C:=Coefficients(Q);
  for i:=1 to #C do
    D:=Coefficients(C[i]);
    for j:=1 to #D do
      Qfun:=Qfun+D[j]*(Qx.1)^(j-1)*(Qxy.1)^(i-1);
    end for;
  end for;
  FF:=FunctionField(Qfun);

  b0fun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W0[i,j]*FF.1^(j-1);
    end for;
    b0fun[i]:=bi;
  end for;

  binffun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+Winf[i,j]*FF.1^(j-1);
    end for;
    binffun[i]:=bi;
  end for;

  for i:=1 to #xvalues do
    places:=Decomposition(FF,Zeros(Qx.1-xvalues[i])[1]);
    if Valuation(xvalues[i],p) ge 0 then
      for j:=1 to #places do
        if Degree(places[j]) eq 1 then
          x:=xvalues[i];
          b:=[];
          for k:=1 to d do
            b[k]:=Evaluate(b0fun[k],places[j]);
          end for;
          P:=set_bad_point(x,b,false,data);
          pointlist:=Append(pointlist,P);
        end if;
      end for;
    else
      for j:=1 to #places do
        if Degree(places[j]) eq 1 then
          x:=1/xvalues[i];
          b:=[];
          for k:=1 to d do
            b[k]:=Evaluate(binffun[k],places[j]);
          end for;
          P:=set_bad_point(x,b,true,data);
          pointlist:=Append(pointlist,P);
        end if;
      end for;
    end if;
  end for; 

  places:=InfinitePlaces(FF);
  for i:=1 to #places do
    if Degree(places[i]) eq 1 then
      x:=0;
      b:=[];
      for j:=1 to d do
        b[j]:=Evaluate(binffun[j],places[i]);
      end for;
      P:=set_bad_point(x,b,true,data);
      pointlist:=Append(pointlist,P);
    end if;
  end for; 

  return pointlist;

end function;


my_roots_Zpt:=function(f)

  // Custom function to compute the roots of a polynomial
  // f over Z_p since the Magma intrinsic requires the leading
  // coefficient to be a unit (which is usually not the case 
  // for us).

  if f eq 0 then
    error "Polynomial has to be non-zero";
  end if;

  Zps:=Parent(f);
  Zp:=BaseRing(Zps);
  Fp:=ResidueClassField(Zp);
  Fps:=PolynomialRing(Fp);
  p:=Characteristic(Fp);
  
  Nf:=Precision(Zp);
  val:=Minimum([Valuation(e):e in Eltseq(f)]);
  Zp:=ChangePrecision(Zp,Nf-val);
  Zps:=PolynomialRing(Zp);
  
  f:=Zps![e/p^val :e in Eltseq(f)];

  i:=0;
  zero:=false;
  done:=false;
  while not done do
    if Coefficient(f,i) ne 0 then
      lcindex:=i;
      done:=true;
    end if;
    i:=i+1;
  end while;
  if lcindex gt 0 then
    coefs:=Coefficients(f);
    for j:=1 to lcindex do
      coefs:=Remove(coefs,1);
    end for;
    f:=Zps!coefs;
    zero:=true;
  end if;

  modproots:=Roots(Fps!f);
  Fproots:=[];
  for i:=1 to #modproots do
    Fproots[i]:=modproots[i][1];
  end for;
  Zproots:=[[*Zp!e,1*]:e in Fproots];
//"Zproots",Zproots;
  i:=1;
  while i le #Zproots do
    z:=Zproots[i][1];
    Nz:=Zproots[i][2];
    v1:=Valuation(Evaluate(f,z));
    v2:=Valuation(Evaluate(Derivative(f),z)); 
    if not (v1 gt 2*v2 and Nz ge v2+1) and (v1 lt Nf-val) then
      Zproots:=Remove(Zproots,i);
      znew:=z+p^Nz*Zps.1;
      g:=Fps![e/p^(Nz): e in Coefficients(Evaluate(f,znew))];
      if g ne 0 then
        Fproots:=Roots(g);
      else
        Fproots:=[[e,1]: e in Fp];
      end if;
      for j:=1 to #Fproots do
        Zproots:=Insert(Zproots,i,[*z+p^Nz*(Zp!Fproots[j][1]),Nz+1*]);
      end for;
    else
      i:=i+1;
    end if;
  end while;

  for i:=1 to #Zproots do
    z:=Zproots[i][1];
    Nz:=Zproots[i][2];
    v1:=Valuation(Evaluate(f,z));
    v2:=Valuation(Evaluate(Derivative(f),z));
    if (v1 lt Nf-val) then
      z:=HenselLift(f,z);
      Zproots[i][1]:=z;
      Zproots[i][2]:=Nf-val-v2;
    else
      Zproots[i][2]:=Nf-val-v2;
    end if;
  end for;

  if zero then
    Zproots:=Append(Zproots,[*Zp!0,Nf-val*]);
  end if;

  return Zproots;

end function;

function roots_Zpt(f)
  // Iterate my_roots_Zpt to catch a bug that causes it 
  // to miss roots in some examples.
  t := Parent(f).1;
  roots := my_roots_Zpt(f);
  all_roots := [];
  while not (Degree(f) lt 1 or IsEmpty(roots)) do
    for root in roots do
      if root[1] notin [pair[1] : pair in all_roots] then
        Append(~all_roots, root);
      end if;
      f := f div (t-root[1]);
    end for;
    if Degree(f) ge 1 then 
      roots := my_roots_Zpt(f);
    end if;
  end while;
  return all_roots;
end function;


basis_kernel:=function(A)

  // Compute a basis for the kernel of the matrix A over Qp

  val:=Minimum([0] cat [Valuation(x) : x in Eltseq(A)]); 
  Qp:=BaseRing(A);
  N:=Precision(Qp);
  p:=Prime(Qp);

  A:=p^(-val)*A; 
  N:=N-val;

  Zp:=pAdicRing(p,N);
  row:=NumberOfRows(A);
  col:=NumberOfColumns(A);
  matpN:=ZeroMatrix(Zp,row,col);
  for i:=1 to row do
    for j:=1 to col do
      matpN[i,j]:=Zp!A[i,j];
    end for;
  end for;
  S,P1,P2:=SmithForm(matpN);            
 
  b:=[];
  for i:=Rank(S)+1 to row do
    Append(~b,P1[i]);
  end for;
  if #b gt 0 then
    b:=RowSequence(HermiteForm(Matrix(b)));
  end if;
 
  b:=RowSequence(ChangeRing(Matrix(b),Qp));

  return b;
end function;


vanishing_differentials:=function(points,data:e:=1);

  // Compute the regular one forms of which the 
  // integrals vanish between all points in points.

  Q:=data`Q; p:=data`p;
  
  g:=genus(Q,p);

  IP1Pi:=[];
  NIP1Pi:=[];
  for i:=1 to #points-1 do
    Ci,Ni:=coleman_integrals_on_basis(points[1],points[i+1],data:e:=e);
    IP1Pi[i]:=Ci;
    NIP1Pi[i]:=Ni;
  end for;

  Nint:=Minimum(NIP1Pi);

  K:=pAdicField(p,Nint);
  M:=ZeroMatrix(K,g,#points-1);
  for i:=1 to g do
    for j:=1 to #points-1 do
      M[i,j]:=K!reduce_mod_pN_Q(Rationals()!IP1Pi[j][i],p,Nint);
    end for;
  end for;

  v:=basis_kernel(M);

  return v,IP1Pi,NIP1Pi;

end function;


zeros_on_disk:=function(P1,P2,v,data:prec:=0,e:=1,integral:=[**]);

  // Find all common zeros of the integrals of the v[i] (vectors 
  // of length g) from P1 to points in the residue disk of P2.

  Q:=data`Q; p:=data`p; N:=data`N; 

  g:=genus(Q,p);

  if integral eq [**] then
    IP1P2,NIP1P2:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  else
    IP1P2:=integral[1];
    NIP1P2:=integral[2];
  end if;
  tinyP2toz,xt,bt,NP2toz:=tiny_integrals_on_basis_to_z(P2,data:prec:=prec);

  Nv:=Precision(Parent(v[1][1]));
  Zp:=pAdicRing(p,Nv);
  Zpt:=PolynomialRing(Zp);

  zerolist:=[];
  for i:=1 to #v do
    f:=Parent(tinyP2toz[1])!0;
    for j:=1 to g do
      f:=f+v[i][j]*(IP1P2[j]+tinyP2toz[j]);
    end for;
    h:=Zpt!0;
    for j:=0 to Degree(f) do
      h:=h+IntegerRing()!(p^j*(RationalField()!Coefficient(f,j)))*Zpt.1^j;
    end for; 
    zeros:=my_roots_Zpt(h);
    zerolist:=Append(zerolist,zeros);
  end for;

  zeroseq:=[];
  for i:=1 to #zerolist[1] do
    allzero:=true;
    for j:=2 to #zerolist do
      found:=false;
      for k:=1 to #zerolist[j] do
        if Valuation(zerolist[j][k][1]-zerolist[1][i][1]) ge Minimum(zerolist[j][k][2],zerolist[1][i][2]) then
          found:=true;
        end if;
      end for;
      if not found then
        allzero:=false;
      end if;
    end for;
    if allzero then
      zeroseq:=Append(zeroseq,zerolist[1][i][1]);
    end if; 
  end for;

  pointlist:=[];
  for i:=1 to #zeroseq do
    z:=zeroseq[i];
    x:=Evaluate(xt,p*z);         
    b:=Eltseq(Evaluate(bt,p*z)); 
    inf:=P2`inf; 
    P:=set_bad_point(x,b,P2`inf,data);
    pointlist:=Append(pointlist,P);
  end for;

  return pointlist;

end function;


effective_chabauty:=function(data:Qpoints:=[],bound:=0,e:=1);

  // Carries out effective Chabauty for the curve given by data.
  // First does a point search up to height bound. Then uses the
  // points found to determine the vanishing differentials. Finally
  // goes over all residue disks mapping to points on the reduction
  // mod p and finds all common zeros of the vanishing differentials.

  if #Qpoints eq 0 then
    if bound eq 0 then
      error "have to specify either Qpoints or a bound for search";
    end if;
    Qpoints:=Q_points(data,bound);
  end if; 
   
  for i:=1 to #Qpoints do
    _,index:=local_data(Qpoints[i],data);
    data:=update_minpolys(data,Qpoints[i]`inf,index);
    if is_bad(Qpoints[i],data) then
      if is_very_bad(Qpoints[i],data) then
        xt,bt,index:=local_coord(Qpoints[i],tadicprec(data,e),data);
        Qpoints[i]`xt:=xt;
        Qpoints[i]`bt:=bt;
        Qpoints[i]`index:=index; 
      end if;
    else
      xt,bt,index:=local_coord(Qpoints[i],tadicprec(data,1),data);
      Qpoints[i]`xt:=xt;
      Qpoints[i]`bt:=bt;
      Qpoints[i]`index:=index; 
    end if;
  end for;

  v,IP1Pi,NIP1Pi:=vanishing_differentials(Qpoints,data:e:=e);

  Qppoints,data:=Qp_points(data:points:=Qpoints);
  for i:=1 to #Qppoints do
    if is_bad(Qppoints[i],data) then
      xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,e),data);
    else
      xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,1),data);
    end if;
    Qppoints[i]`xt:=xt;
    Qppoints[i]`bt:=bt;
    Qppoints[i]`index:=index;
  end for;

  pointlist:=[];
  for i:=1 to #Qppoints do
    k:=0;
    for j:=1 to #Qpoints do
      if (Qppoints[i]`x eq Qpoints[j]`x) and (Qppoints[i]`b eq Qpoints[j]`b) and (Qppoints[i]`inf eq Qpoints[j]`inf) then
        k:=j;
      end if;
    end for;
    if k lt 2 then
      pts:=zeros_on_disk(Qpoints[1],Qppoints[i],v,data:e:=e);
    else
      pts:=zeros_on_disk(Qpoints[1],Qppoints[i],v,data:e:=e,integral:=[*IP1Pi[k-1],NIP1Pi[k-1]*]);
    end if;
    for j:=1 to #pts do
      pointlist:=Append(pointlist,pts[j]);
    end for;
  end for;

  return pointlist, v;

end function;


torsion_packet:=function(P,data:bound:=0,e:=1);

  // Compute the rational points in the torsion packet of P
  // by computing the common zeros of the integrals of all
  // regular 1-forms from P to an arbitrary point in a residue
  // disk maping to points on the reduction mod p.

  Q:=data`Q; p:=data`p; N:=data`N;
  Qp:=pAdicField(p,N);

  g:=genus(Q,p);
  v:=RowSequence(IdentityMatrix(Qp,g));

  _,index:=local_data(P,data);
  data:=update_minpolys(data,P`inf,index);
  if is_bad(P,data) then
    if is_very_bad(P,data) then
      xt,bt,index:=local_coord(P,tadicprec(data,e),data);
      P`xt:=xt;
      P`bt:=bt;
      P`index:=index;
    end if;
  else
    xt,bt,index:=local_coord(P,tadicprec(data,1),data);
    P`xt:=xt;
    P`bt:=bt;
    P`index:=index;
  end if;

  if bound ne 0 then
    Qpoints:=Q_points(data,bound); 
    Qppoints,data:=Qp_points(data:points:=Qpoints);
  else
    Qppoints,data:=Qp_points(data);
  end if;

  for i:=1 to #Qppoints do
    if is_bad(Qppoints[i],data) then
      if is_very_bad(Qppoints[i],data) then
        xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,e),data);
        Qppoints[i]`xt:=xt;
        Qppoints[i]`bt:=bt;
        Qppoints[i]`index:=index;
      end if;
    else
      xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,1),data);
      Qppoints[i]`xt:=xt;
      Qppoints[i]`bt:=bt;
      Qppoints[i]`index:=index;
    end if;
  end for;
  
  pointlist:=[];
  for i:=1 to #Qppoints do
    pts:=zeros_on_disk(P,Qppoints[i],v,data:e:=e);
    for j:=1 to #pts do
      pointlist:=Append(pointlist,pts[j]);
    end for;
  end for;

  return pointlist;

end function;


function separate(L)
  // L is a sequence of p-adic integers.
  // Return a sequence S of integers such that L[i] 
  // is not congruent to any L[j] modulo p^(S[i]).
  //assert #L eq #SequenceToSet(L); 
  p := Prime(Universe(L));
  min_prec := Min([Precision(Parent(l)) : l in L]);
  ChangeUniverse(~L, pAdicField(p, min_prec));
  return [Max([Valuation(l - m) : m in L | m ne l]) : l in L];
end function;


function roots_with_prec(G, N)
  // return the integral roots of a p-adic polynomial f, and the precision
  // to which they are known.
  // As in Lemma 4.7, our G(t) is F(pt)
  // We throw an error if there are multiple roots 
  coeffsG := Coefficients(G);
  p := Prime(Universe(coeffsG));
  Qp := pAdicField(p,N); 
  Qptt := PowerSeriesRing(Qp);
  Zp := pAdicRing(p,N);
  Zpt := PolynomialRing(Zp);
  Qpt := PolynomialRing(Qp);
  precG := #coeffsG;
  min_val := Min([Valuation(c) : c in coeffsG]); // this is k in Lemma 4.7
  max_N_index := Max([i : i in [1..precG] | Valuation(coeffsG[i]) le N]);
  // TODO: Could lower t-adic precision according to Lemma 4,7. 
  valG := Min(0, Valuation(G));
  G_poly := Zpt!(p^(-min_val)*Qpt.1^valG*(Qpt![Qp!c : c in coeffsG ])); 
  G_series := (p^(-min_val)*Qptt.1^valG*(Qptt![Qp!c : c in coeffsG ])); 
  upper_bd_number_of_roots := count_roots_in_unit_ball(G_poly, N-min_val); 
  if upper_bd_number_of_roots eq 0 then 
    return [], N, G_series;
  end if;
  roots := roots_Zpt(G_poly);  // compute the roots.
  assert &and[z[2] gt 0 : z in roots]; // First check that roots are simple.
  if #roots gt 0 then 
    root_prec := Floor((N - min_val)/#roots); // Lemma 4.7
    vals := [Valuation(rt[1]) : rt in roots];
    compare_vals(ValuationsOfRoots(G_poly), vals, root_prec);
    if #roots gt 0 and root_prec le 0 then
      error "Precision of roots too small. Rerun with higher p-adic pre (parameter N)";
    end if;
  else  // no root, so no precision loss.
    root_prec := N;
  end if;
  return roots, root_prec, G_series;
end function;

    
