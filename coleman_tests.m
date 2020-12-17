load "coleman.m";


// These are tests for the Coleman integration code, not quadratic Chabauty

print "";
print "//////////////////////////";
print "// 1. An elliptic curve //";
print "//////////////////////////\n";

Q:=y^2-(x^3-10*x+9);
p:=5;
N:=10;
data:=coleman_data(Q,p,N);

print "/////////////////////";
print "// 1a. good points //";
print "/////////////////////\n";

P1:=set_point(0,3,data);  // not bad
P2:=set_point(8,21,data); // not bad
C:=coleman_integrals_on_basis(P1,P2,data);
C;
print "(O(5^9) 6 + O(5^9))\n";

print "//////////////////////////";
print "// 1b. finite bad point //";
print "//////////////////////////\n";

P3:=set_bad_point(1,[1,0],false,data); // finite bad
C:=coleman_integrals_on_basis(P1,P3,data:e:=51);
C;
print "(-7179*5^2 + O(5^8) 11778*5 + O(5^8))\n";

print "////////////////////////";
print "// 1c. infinite point //";
print "////////////////////////\n";

P4:=set_bad_point(0,[1,0],true,data); // infinite
C:=coleman_integrals_on_basis(P2,P4,data:e:=11); 
C;
print "(-38429*5^2 + O(5^9) 449509 + O(5^9))\n";


print "///////////////////////////////////////////////";
print "// 2. Bruin-Poonen-Stoll (Winf not diagonal) //";
print "///////////////////////////////////////////////\n";

Q:=y^3 + (-x^2 - 1)*y^2 - x^3*y + x^3 + 2*x^2 + x;
p:=7;
N:=10;
Qp:=pAdicField(p,N);
data:=coleman_data(Q,p,N);

print "/////////////////////";
print "// 2a. good points //";
print "/////////////////////\n";

P1:=set_point(5,-32582624253112412,data);
P2:=set_point(12,25123732258943588,data);
C:=coleman_integrals_on_basis(P1,P2,data);
T:=tiny_integrals_on_basis(P1,P2,data);
C-T;
print "(O(7^8) O(7^8) O(7^8) O(7^8) O(7^8) O(7^8))\n";

print "///////////////////////////";
print "// 2b. finite bad points //";
print "///////////////////////////\n";

P3:=set_point(0,0,data); // finite bad
P4:=set_point(0,1,data); // finite bad
C:=coleman_integrals_on_basis(P1,P3,data:e:=100); 
C;
print "(197200*7 + O(7^8) -2355398 + O(7^8) 2318140 + O(7^8) -114216*7 + O(7^8) 6600662*7^-1 + O(7^8) 14277898*7^-1 + O(7^8))\n";
C:=coleman_integrals_on_basis(P1,P4,data:e:=100);
C;
print "(-28265*7 + O(7^8) -1950909 + O(7^8) -581178 + O(7^8) 1730082 + O(7^8) 18808679*7^-1 + O(7^8) -7433096*7^-1 + O(7^8))\n";

print "//////////////////////////////////////////";
print "// 2c. infinite points (all unramified) //";
print "//////////////////////////////////////////\n";

P5:=set_bad_point(0,[1,0,1],true,data); // infinite
P6:=set_bad_point(0,[1,1,1],true,data); // infinite
P7:=set_bad_point(0,[1,0,0],true,data); // infinite

C:=coleman_integrals_on_basis(P1,P5,data:e:=100);
C;
print "(15716*7^2 + O(7^8) -1514399 + O(7^8) -1180876 + O(7^8) 1578602 + O(7^8) 7286411*7^-1 + O(7^8) 18981542*7^-1 + O(7^8))\n";
C:=coleman_integrals_on_basis(P1,P6,data:e:=100);
C;
print "(-378393*7 + O(7^8) -548262 + O(7^8) -797606 + O(7^8) -1917093 + O(7^8) -720359*7^-1 + O(7^8) 14220357*7^-1 + O(7^8))\n";
C:=coleman_integrals_on_basis(P1,P7,data:e:=100);
C;
print "(-189027*7 + O(7^8) 1165757 + O(7^8) 268783 + O(7^8) 469549 + O(7^8) -14909656*7^-1 + O(7^8) -12079199*7^-1 + O(7^8))\n";


print "/////////////////////////////////////////////////////";
print "// 3. modular curve X0(44) (plane model singular!) //";
print "/////////////////////////////////////////////////////\n";

Q:=y^5+12*x^2*y^3-14*x^2*y^2+(13*x^4+6*x^2)*y-(11*x^6+6*x^4+x^2);
p:=7;
N:=10;
data:=coleman_data(Q,p,N);

print "/////////////////////";
print "// 3a. good points //";
print "/////////////////////\n";

P1:=set_point(1,1,data);
P2:=set_point(8,29647929146699830,data);
C:=coleman_integrals_on_basis(P1,P2,data);
T:=tiny_integrals_on_basis(P1,P2,data);
C-T;
print "(O(7^8) O(7^8) O(7^8) O(7^8) O(7^8) O(7^8) O(7^8) O(7^8))\n";

print "//////////////////////////";
print "// 3b. finite bad point //";
print "//////////////////////////\n";

P3:=set_bad_point(0,[1,0,0,0,0],false,data); // finite bad
C:=coleman_integrals_on_basis(P1,P3,data:e:=100); // (15(P3-P1)=O on the Jacobian!)
C;
print "(O(7^5) O(7^5) O(7^5) O(7^5) -7124 + O(7^5) 55837*7^-1 + O(7^5) -682 + O(7^5) 30395*7^-1 + O(7^5))\n";

print "////////////////////////"; 
print "// 3c. infinite point //";
print "////////////////////////\n";

P4:=set_bad_point(0,[1,0,0,0,0],true,data); // infinite
C:=coleman_integrals_on_basis(P1,P4,data:e:=100); // (15(P4-P1)=O on the Jacobian!)
C;
print "(O(7^7) O(7^7) O(7^7) O(7^7) -272863 + O(7^7) 1114678*7^-1 + O(7^7) 182353 + O(7^7) 2383375*7^-1 + O(7^7))\n";
