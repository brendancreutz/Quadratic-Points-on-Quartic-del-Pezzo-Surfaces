//dP4QuadPts.m
//Brendan Creutz 23/09/2024
/*
This magma file contains code and computations and code related to the paper:
[CV24] "Quartic del Pezzo surfaces without quadratic points" by Brendan Creutz and Bianca Viray, arXiv:2408.08436

For Magma Version: V2.28-9

Anyone is free to adapt and use this code.
Not guaranteed to be bug free!
*/

_<T> := PolynomialRing(Rationals());
_<u0,u1,u2,u3,u4> := PolynomialRing(Rationals(),5);
f2 := T^2 + 3;
f3 := T^3 + 3*T^2 + 3*T - 9;
f := f2*f3;
k2 := NumberField(f2);
k3 := NumberField(f3);
eps3 := Roots(f3,k3)[1][1];
assert Norm(eps3) eq 9;

// We consider a family of quartic del Pezzo surface X_d : Q0 = Qinf = 0
// The singular quadrics in the pencil occur at roots of f
// Discriminants of the singular quadrics are d,eps3

R<t,d> := PolynomialRing(k3,2);
minf := Matrix(5,5,
[ 0 , -d , 0 , 0 , 0] cat 
[ -d , 0 , 0 , 0 , 0] cat
[ 0 , 0 ,1 , 0 , -1] cat
[ 0 , 0 , 0 , -3 , 0] cat
[ 0 , 0 , -1 , 0 ,-1]
);
m0 := Matrix(5,5,
[ d , 0 , 0 , 0 , 0] cat
[ 0 ,-3*d, 0 , 0 , 0] cat
[ 0 , 0 , 6 , 3 , 0] cat
[ 0 , 0 , 3 , 0 ,-3] cat
[ 0 , 0 , 0 ,-3 , 0]
);
// m0 and minf are symmetric matrices corresponding to Q0, Qinf
fd := Determinant(m0 + t*minf);
assert fd eq -6*d^2*Evaluate(f,R.1);
// Checks that the singular quadrics are indeed above roots of f
mscrt := m0 + k3.1*minf;
assert Rank(mscrt) eq 4;
Qscrt := QuadraticForm(Diagonalization(mscrt));
dQscrt := &*Coefficients(Qscrt);
c := Evaluate(dQscrt,[0,1]);
assert IsSquare(k3!c*eps3);
assert dQscrt eq c*d^2;
// Checks that the discriminant of the degree 3 singular quadric is eps3.

// Now we do this for the degree 2 singular quadric:
R<t,d> := PolynomialRing(k2,2);
minf := Matrix(5,5,
[ 0 , -d , 0 , 0 , 0] cat 
[ -d , 0 , 0 , 0 , 0] cat
[ 0 , 0 ,1 , 0 , -1] cat
[ 0 , 0 , 0 , -3 , 0] cat
[ 0 , 0 , -1 , 0 ,-1]
);
m0 := Matrix(5,5,
[ d , 0 , 0 , 0 , 0] cat
[ 0 ,-3*d, 0 , 0 , 0] cat
[ 0 , 0 , 6 , 3 , 0] cat
[ 0 , 0 , 3 , 0 ,-3] cat
[ 0 , 0 , 0 ,-3 , 0]
);
fd := Determinant(m0 + t*minf);
assert fd eq -6*d^2*Evaluate(f,R.1);
mscrt := m0 + k2.1*minf;
assert Rank(mscrt) eq 4;
Qscrt := QuadraticForm(Diagonalization(mscrt));
dQscrt := &*Coefficients(Qscrt);
c := Evaluate(dQscrt,[0,1]);
assert IsSquare(k2!c);
assert dQscrt eq c*d;
// Checks that the discriminant is in fact d.


ConditionsOnd := function(d);
//Checks if d satisfies the conditions of [CV24, Theorem 6]
	if d mod 12 ne 5 then 
		return false;
	end if;
	if not (d eq SquareFree(d)) then
		return false;
	end if;
	for p in [ pp[1] : pp in Factorization(d) ] do
		Ps := Decomposition(k3,p);
		for P in Ps do
			kP,mP := Completion(k3,P[1]);
			if not IsSquare(mP(eps3)) then
				return false;
			end if;
		end for;
	end for;
	return true;
end function;

CheckSdel := function(del2,del3);
/* 
Computes equations for the dP4 with discriminant (del2,del3) in k2*k3 and
checks if there is a likely BM obstruction to quadratic points.
*/
k2 := NumberField(Parent(del2));
k3 := NumberField(Parent(del3));
f2 := DefiningPolynomial(k2);
f3 := DefiningPolynomial(k3);
assert IsSquare(Norm(del3));
L := quo<Parent(f)|f>;
A,toA := AbsoluteAlgebra(L : Fields := {k2,k3});
K2 := A[1];
K3 := A[2];
assert Degree(K2) eq 2;
del := (A! <del2,del3>) @@ toA;
R<x1,x2,x3,u0,u1,u2,u3,u4> := PolynomialRing(L,8);
RL,mRL := SwapExtension(R);
M<t> := PolynomialRing(Rationals(),1);
S<v0,v1,v2,v3,v4> := PolynomialRing(Rationals(),5);
GetdP4fromDel := function(del);
	eq1 := (x1-L.1*x3)*(x2-L.1*x3) - del*(u0+u1*L.1+u2*L.1^2+u3*L.1^3+u4*L.1^4)^2;
	quadsu := Coefficients(mRL(eq1));
	M1 := Eltseq(SymmetricMatrix(Evaluate(quadsu[4],[0,0,0,v0,v1,v2,v3,v4])));
	M2 := Eltseq(SymmetricMatrix(Evaluate(quadsu[5],[0,0,0,v0,v1,v2,v3,v4])));
	L1 := [ M1[i] : i in [1] cat [6,7] cat [11..13] cat [16..19] cat [21..25] ];
	L2 := [ -M2[i] : i in [1] cat [6,7] cat [11..13] cat [16..19] cat [21..25]  ];
	penM := Matrix(5,5,[ M1[i] + t*M2[i] : i in [1..#M1] ]);
	return L1,L2,penM;
end function;
L1,L2,penM := GetdP4fromDel(del);
c1 := LCM([Denominator(a) : a in L1 ]);
c2 := LCM([Denominator(a) : a in L2 ]);
L1 := [ c1*a : a in L1 ];
L2 := [ c2*a : a in L2 ];
Q1 := QuadraticForm(SymmetricMatrix(L1));
Q2 := Parent(Q1)!QuadraticForm(SymmetricMatrix(L2));
P4 := PolynomialRing(Integers(),5);
Q0 := Evaluate(Q1,[P4.i : i in [1..5]]);
Qinf := Evaluate(Q2,[P4.i : i in [1..5]]);
qs := [Q0,Qinf];
SingQs := Determinant(SymmetricMatrix(qs[1])+ T*SymmetricMatrix(qs[2]));
fnew := Factorization(SingQs);
f2new := fnew[1][1];
f3new := fnew[2][1];
k2new := NumberField(f2new);
assert Degree(f2new) eq 2;
P4Q<X0,X1,X2,X3,X4> := ProjectiveSpace(Rationals(),4);
X := Scheme(P4Q,qs);

Qab := function(a,b);
	// Returns the quadric bQ0 + aQinf
	return QuadraticForm(b*SymmetricMatrix(Q0)+ a*SymmetricMatrix(Qinf));
end function;

Gtsolp := function(a,b,p);
	//Returns 1 if the quadric b*Q0 + a*Qinf has a Q_p-line and -1 otherwise.
	//This is for the quadric above (a:b) in P^1
	SS := HilbertSymbol(Rationals()!-1,Rationals()!-1,p);
	Qa := Diagonalization(b*SymmetricMatrix(Q0)+a*SymmetricMatrix(Qinf));
	cfs := Coefficients(QuadraticForm(Qa));
	if 0 in cfs then 
		"error 0";
	end if;
	for i in [1..5] do
		for j in [i+1..5] do
			SS *:= HilbertSymbol(cfs[i],cfs[j],p);
		end for;
	end for;
	return SS;
end function;

Btau := function(a,b,p);
	//return inv_p Beta_tau(P) where P -> (a:b) in P^1.
	gab := &+[ b^(2-i)*a^(i)*Coefficients(f2new)[i+1] : i in [0..2]  ];
	return HilbertSymbol(Rationals()!del2,Rationals()!gab,p);
end function;

BadPs := { -1,2 } join { p[1] : p in Factorization(Integers()!del2) } join { p[1] : p in Factorization(Integers()!Discriminant(f)) };
B := 50; // Look for Qp points above points in P^1 of height at most B
Valsp := [];

for p in BadPs do		
	Vals := {};
	count := 0;
	//Qplines := [];
	// Find some fibers with Qp lines:
	for a in [0..B] do
		if #Vals ge 2 then break; end if;
		for b in [ b : b in [1..B] | GCD(a,b) eq 1 ] do
			if #Vals ge 2 then break; end if;
			if Gtsolp(a,b,p) eq 1 then
				count +:= 1;
				//Qplines cat:= [ [a,b] ];
				Vals join:= { Btau(a,b,p) };
			end if;
			if Gtsolp(-a,b,p) eq 1 then
				count +:= 1;
				//Qplines cat:= [ [a,b] ];
				Vals join:= { Btau(-a,b,p) };
			end if;
		end for;
	end for;
	if Gtsolp(0,1,p) eq 1 then
		count +:= 1;
		//Qplines cat:= [ [a,b] ];
		Vals join:= { Btau(0,1,p) };
	end if;
	Valsp cat:= [ [*p,Vals*] ];
	printf "  At p = %o found %o fibers of height < %o with lines.\n  invariants = %o.\n",p,count,B,Vals;
end for;

Nv,q := Max([#pv[2] : pv in Valsp]);
if Nv eq 2 then
	printf "  Evaluation map is surjective at p = %o.\n\n",Valsp[q][1];
	return Valsp;
end if;
evs := &*[ Random(pv[2]) : pv in Valsp ];
if evs eq -1 then
	printf "  Suspected BM obstruction to lines.\n\n";
	return 	Valsp;
else
	printf "  No BM obstruction to lines.\n\n";
	return Valsp;
end if;
end function; //CheckSdel

/* Example usage of CheckSdel:
del2 := k2 ! -7;
del3 := k3 ! k3.1;
CheckSdel(del2,del3);
*/

CheckSdels := function(N);
ds := [ d : d in [-N..N] | ConditionsOnd(d) ];
for d in ds do
	printf "Checking surface Xd for d = %o\n", d;
	Valsp := CheckSdel(k2!d,k3.1);
	Nv,q := Max([#pv[2] : pv in Valsp]);
	if Nv eq 2 then
		printf "Evaluation map is surjective at p = %o,d = %o.\n\n",Valsp[q][1],d;
		assert false; //Contradicts [CV24, Theorem 6]
	end if;
	evs := &*[ Random(pv[2]) : pv in Valsp ];
	assert evs eq -1;
end for;
return true;
end function;
//CheckSdels(1000);
//Previous line will check that the surfaces in [CV24,Theorem 6] have likely BM obstruction to quadratic points for all d < 1000.

////////////////
////////////////
//Below is code related to existence of degree 6 points on the surfaces Xd
CubicPointsG := function(d,B);
	// A function looks for k3-points on G, the symmetric square of Xd
	// It checks for fibers of small height (related to B) where G has a point over k3
	minf := Matrix(5,5,
		[ 0 , -d , 0 , 0 , 0] cat 
		[ -d , 0 , 0 , 0 , 0] cat
		[ 0 , 0 ,1 , 0 , -1] cat
		[ 0 , 0 , 0 , -3 , 0] cat
		[ 0 , 0 , -1 , 0 ,-1]
		);
	m0 := Matrix(5,5,
		[ d , 0 , 0 , 0 , 0] cat
		[ 0 ,-3*d, 0 , 0 , 0] cat
		[ 0 , 0 , 6 , 3 , 0] cat
		[ 0 , 0 , 3 , 0 ,-3] cat
		[ 0 , 0 , 0 ,-3 , 0]
		);
	Q0 := QuadraticForm(m0);
	Qinf := QuadraticForm(minf);
	
	Solubleab := function(a,b);
		//Check if there is a line on the fiber above (a:b) in P1
		Qab := QuadraticForm(Diagonalization(b*SymmetricMatrix(Q0)+ a*SymmetricMatrix(Qinf)));
		cfs := Coefficients(Qab);
		BadP := [ P[1] : P in Factorization( (2*&*cfs)*Integers(k3))];
		//Remark: there is 1 real prime which we will ignore because of reciprocity
		for P in BadP do
			//Check if Qab has a line over the completion of k3 at P:
			SS := HilbertSymbol(k3!-1,k3!-1,P);
			if 0 in cfs then 
				"error 0";
				assert false;
			end if;
			for i in [1..5] do
				for j in [i+1..5] do
					SS *:= HilbertSymbol(k3!cfs[i],k3!cfs[j],P);
				end for;
			end for;
			if SS eq -1 then
				// not soluble at P
				//printf "Not soluble at P = %o\n",P;
				return false;
			end if;
		end for;
		return true;
	end function;
	
	SolubleFibers := [];
	// Search for soluble fibers:
	for c1 in [1..B] do
		for c2 in [1..B] do
			if Solubleab(c1*k3.1 + 3*c2,Abs(d)) then
				SolubleFibers cat:= [ [c1*k3.1 + 3*c2,k3!Abs(d)] ];
			end if;
			if Solubleab(-c1*k3.1 - 3*c2,Abs(d)) then
				SolubleFibers cat:= [ [c1*k3.1 + 3*c2,k3!Abs(d)] ];
			end if;
		end for;
	end for;
	return SolubleFibers;
end function;


/*
The following function looks for k3-points on the BS-fibrations G associated to the surfaces Xd
for d in [-N..N] satisfying the conditions of [CV24, Theorem 6] it looks for fibers of G -> P1 of small
height which contain k3-points.

Data for N = 1000 is given after the function.
*/

Checkds := function(N);
deg6pts := [];
ds := [ d : d in [-N..N] | ConditionsOnd(d) ];		
for d in ds do
	dpt := [];
	B := 3;
	printf " Checking for d = %o\n",d;
	while #dpt eq 0 do
		dpt := CubicPointsG(d,B);
		if #dpt gt 0 then 
			deg6pts cat:= [ [*d,dpt *]];
		end if;
		B *:= 2;
		printf "  Increasing bound...\n";
		if B gt 2^6*3 then 
			printf "  giving up...\n\n"; break; end if;
	end while;
end for;
return deg6pts;
end function;

/*
This gives pairs: [* d, [pts]] where
	d satisfies the conditions of [CV24, Theorem 6] and 
	[pts] are coordinates of points in P^1(k3) where G_t(k3) is nonempty
	It gives such points for all |d| < 1000
*/
deg6pts:=
[ [* -991,
    [
        [
            8*k3.1 + 3,
            991
        ]
    ]
*], [* -979,
    [
        [
            4*k3.1 + 45,
            979
        ],
        [
            4*k3.1 + 51,
            979
        ]
    ]
*], [* -955,
    [
        [
            2*k3.1 + 9,
            955
        ]
    ]
*], [* -919,
    [
        [
            11*k3.1 + 9,
            919
        ]
    ]
*], [* -883,
    [
        [
            2*k3.1 + 9,
            883
        ]
    ]
*], [* -871,
    [
        [
            5*k3.1 + 36,
            871
        ]
    ]
*], [* -823,
    [
        [
            k3.1 + 18,
            823
        ]
    ]
*], [* -811,
    [
        [
            11*k3.1 + 45,
            811
        ]
    ]
*], [* -787,
    [
        [
            k3.1 + 42,
            787
        ],
        [
            7*k3.1 + 57,
            787
        ],
        [
            13*k3.1 + 27,
            787
        ],
        [
            14*k3.1 + 39,
            787
        ],
        [
            19*k3.1 + 51,
            787
        ]
    ]
*], [* -763,
    [
        [
            10*k3.1 + 57,
            763
        ],
        [
            13*k3.1 + 45,
            763
        ],
        [
            23*k3.1 + 63,
            763
        ]
    ]
*], [* -727,
    [
        [
            4*k3.1 + 33,
            727
        ]
    ]
*], [* -715,
    [
        [
            4*k3.1 + 69,
            715
        ]
    ]
*], [* -679,
    [
        [
            20*k3.1 + 33,
            679
        ],
        [
            23*k3.1 + 48,
            679
        ]
    ]
*], [* -667,
    [
        [
            k3.1 + 27,
            667
        ],
        [
            7*k3.1 + 15,
            667
        ]
    ]
*], [* -631,
    [
        [
            7*k3.1 + 6,
            631
        ]
    ]
*], [* -619,
    [
        [
            4*k3.1 + 45,
            619
        ],
        [
            13*k3.1 + 63,
            619
        ],
        [
            22*k3.1 + 69,
            619
        ]
    ]
*], [* -595,
    [
        [
            4*k3.1 + 21,
            595
        ]
    ]
*], [* -571,
    [
        [
            10*k3.1 + 33,
            571
        ]
    ]
*], [* -559,
    [
        [
            7*k3.1 + 33,
            559
        ]
    ]
*], [* -547,
    [
        [
            5*k3.1 + 39,
            547
        ],
        [
            5*k3.1 + 57,
            547
        ],
        [
            13*k3.1 + 24,
            547
        ],
        [
            16*k3.1 + 33,
            547
        ],
        [
            20*k3.1 + 3,
            547
        ],
        [
            22*k3.1 + 69,
            547
        ]
    ]
*], [* -523,
    [
        [
            4*k3.1 + 21,
            523
        ]
    ]
*], [* -499,
    [
        [
            10*k3.1 + 33,
            499
        ]
    ]
*], [* -487,
    [
        [
            5*k3.1 + 33,
            487
        ]
    ]
*], [* -463,
    [
        [
            8*k3.1 + 21,
            463
        ],
        [
            11*k3.1 + 6,
            463
        ]
    ]
*], [* -439,
    [
        [
            4*k3.1 + 33,
            439
        ],
        [
            11*k3.1 + 30,
            439
        ]
    ]
*], [* -427,
    [
        [
            7*k3.1 + 3,
            427
        ],
        [
            8*k3.1 + 9,
            427
        ]
    ]
*], [* -403,
    [
        [
            5*k3.1 + 72,
            403
        ],
        [
            23*k3.1 + 18,
            403
        ]
    ]
*], [* -391,
    [
        [
            19*k3.1 + 69,
            391
        ]
    ]
*], [* -379,
    [
        [
            11*k3.1 + 48,
            379
        ],
        [
            16*k3.1 + 33,
            379
        ],
        [
            17*k3.1 + 39,
            379
        ],
        [
            17*k3.1 + 57,
            379
        ]
    ]
*], [* -367,
    [
        [
            5*k3.1 + 3,
            367
        ]
    ]
*], [* -331,
    [
        [
            4*k3.1 + 51,
            331
        ],
        [
            20*k3.1 + 3,
            331
        ]
    ]
*], [* -319,
    [
        [
            8*k3.1 + 3,
            319
        ]
    ]
*], [* -307,
    [
        [
            5*k3.1 + 42,
            307
        ],
        [
            5*k3.1 + 69,
            307
        ],
        [
            16*k3.1 + 15,
            307
        ]
    ]
*], [* -283,
    [
        [
            10*k3.1 + 33,
            283
        ]
    ]
*], [* -271,
    [
        [
            5*k3.1 + 15,
            271
        ]
    ]
*], [* -247,
    [
        [
            k3.1 + 18,
            247
        ],
        [
            4*k3.1 + 15,
            247
        ]
    ]
*], [* -223,
    [
        [
            4*k3.1 + 33,
            223
        ]
    ]
*], [* -211,
    [
        [
            4*k3.1 + 27,
            211
        ],
        [
            7*k3.1 + 3,
            211
        ],
        [
            11*k3.1 + 24,
            211
        ]
    ]
*], [* -199,
    [
        [
            5*k3.1 + 33,
            199
        ],
        [
            7*k3.1 + 15,
            199
        ]
    ]
*], [* -187,
    [
        [
            5*k3.1 + 66,
            187
        ],
        [
            10*k3.1 + 57,
            187
        ],
        [
            22*k3.1 + 69,
            187
        ],
        [
            23*k3.1 + 12,
            187
        ]
    ]
*], [* -163,
    [
        [
            16*k3.1 + 15,
            163
        ],
        [
            17*k3.1 + 3,
            163
        ],
        [
            20*k3.1 + 3,
            163
        ]
    ]
*], [* -151,
    [
        [
            5*k3.1 + 3,
            151
        ]
    ]
*], [* -115,
    [
        [
            4*k3.1 + 45,
            115
        ],
        [
            4*k3.1 + 51,
            115
        ],
        [
            4*k3.1 + 69,
            115
        ],
        [
            5*k3.1 + 39,
            115
        ],
        [
            5*k3.1 + 57,
            115
        ],
        [
            10*k3.1 + 57,
            115
        ],
        [
            11*k3.1 + 54,
            115
        ],
        [
            13*k3.1 + 18,
            115
        ],
        [
            22*k3.1 + 69,
            115
        ],
        [
            23*k3.1 + 9,
            115
        ]
    ]
*], [* -91,
    [
        [
            7*k3.1 + 33,
            91
        ]
    ]
*], [* -67,
    [
        [
            5*k3.1 + 21,
            67
        ],
        [
            7*k3.1 + 21,
            67
        ],
        [
            8*k3.1 + 9,
            67
        ],
        [
            10*k3.1 + 33,
            67
        ]
    ]
*], [* -55,
    [
        [
            5*k3.1 + 6,
            55
        ]
    ]
*], [* -43,
    [
        [
            5*k3.1 + 21,
            43
        ],
        [
            8*k3.1 + 15,
            43
        ]
    ]
*], [* -31,
    [
        [
            4*k3.1 + 33,
            31
        ],
        [
            8*k3.1 + 3,
            31
        ],
        [
            11*k3.1 + 6,
            31
        ]
    ]
*], [* -19,
    [
        [
            8*k3.1 + 39,
            19
        ],
        [
            11*k3.1 + 45,
            19
        ],
        [
            13*k3.1 + 48,
            19
        ],
        [
            16*k3.1 + 15,
            19
        ],
        [
            20*k3.1 + 21,
            19
        ],
        [
            20*k3.1 + 45,
            19
        ]
    ]
*], [* -7,
    [
        [
            4*k3.1 + 9,
            7
        ],
        [
            5*k3.1 + 3,
            7
        ]
    ]
*], [* 5,
    [
        [
            k3.1 + 63,
            5
        ],
        [
            5*k3.1 + 39,
            5
        ],
        [
            17*k3.1 + 18,
            5
        ],
        [
            17*k3.1 + 30,
            5
        ],
        [
            17*k3.1 + 39,
            5
        ],
        [
            19*k3.1 + 6,
            5
        ],
        [
            19*k3.1 + 72,
            5
        ],
        [
            23*k3.1 + 27,
            5
        ]
    ]
*], [* 17,
    [
        [
            k3.1 + 24,
            17
        ],
        [
            7*k3.1 + 33,
            17
        ],
        [
            8*k3.1 + 3,
            17
        ],
        [
            11*k3.1 + 30,
            17
        ]
    ]
*], [* 29,
    [
        [
            k3.1 + 12,
            29
        ]
    ]
*], [* 65,
    [
        [
            5*k3.1 + 21,
            65
        ],
        [
            7*k3.1 + 33,
            65
        ]
    ]
*], [* 77,
    [
        [
            7*k3.1 + 21,
            77
        ]
    ]
*], [* 89,
    [
        [
            7*k3.1 + 6,
            89
        ],
        [
            11*k3.1 + 12,
            89
        ]
    ]
*], [* 113,
    [
        [
            5*k3.1 + 21,
            113
        ],
        [
            8*k3.1 + 3,
            113
        ],
        [
            11*k3.1 + 6,
            113
        ]
    ]
*], [* 161,
    [
        [
            11*k3.1 + 63,
            161
        ],
        [
            16*k3.1 + 45,
            161
        ],
        [
            16*k3.1 + 51,
            161
        ],
        [
            17*k3.1 + 3,
            161
        ]
    ]
*], [* 173,
    [
        [
            2*k3.1 + 3,
            173
        ]
    ]
*], [* 209,
    [
        [
            13*k3.1 + 63,
            209
        ],
        [
            17*k3.1 + 42,
            209
        ],
        [
            17*k3.1 + 51,
            209
        ],
        [
            23*k3.1 + 45,
            209
        ],
        [
            23*k3.1 + 63,
            209
        ]
    ]
*], [* 221,
    [
        [
            8*k3.1 + 9,
            221
        ]
    ]
*], [* 257,
    [
        [
            5*k3.1 + 21,
            257
        ]
    ]
*], [* 269,
    [
        [
            5*k3.1 + 15,
            269
        ]
    ]
*], [* 281,
    [
        [
            5*k3.1 + 21,
            281
        ],
        [
            7*k3.1 + 6,
            281
        ]
    ]
*], [* 305,
    [
        [
            k3.1 + 27,
            305
        ]
    ]
*], [* 317,
    [
        [
            k3.1 + 12,
            317
        ]
    ]
*], [* 341,
    [
        [
            2*k3.1 + 3,
            341
        ]
    ]
*], [* 353,
    [
        [
            4*k3.1 + 15,
            353
        ]
    ]
*], [* 377,
    [
        [
            7*k3.1 + 6,
            377
        ],
        [
            8*k3.1 + 3,
            377
        ],
        [
            11*k3.1 + 12,
            377
        ]
    ]
*], [* 437,
    [
        [
            5*k3.1 + 66,
            437
        ],
        [
            17*k3.1 + 3,
            437
        ],
        [
            17*k3.1 + 39,
            437
        ],
        [
            19*k3.1 + 51,
            437
        ]
    ]
*], [* 449,
    [
        [
            8*k3.1 + 3,
            449
        ]
    ]
*], [* 473,
    [
        [
            8*k3.1 + 3,
            473
        ]
    ]
*], [* 485,
    [
        [
            5*k3.1 + 15,
            485
        ]
    ]
*], [* 521,
    [
        [
            k3.1 + 24,
            521
        ]
    ]
*], [* 545,
    [
        [
            5*k3.1 + 21,
            545
        ]
    ]
*], [* 569,
    [
        [
            4*k3.1 + 63,
            569
        ],
        [
            13*k3.1 + 45,
            569
        ],
        [
            13*k3.1 + 60,
            569
        ],
        [
            19*k3.1 + 66,
            569
        ]
    ]
*], [* 641,
    [
        [
            5*k3.1 + 39,
            641
        ],
        [
            13*k3.1 + 63,
            641
        ],
        [
            16*k3.1 + 27,
            641
        ],
        [
            16*k3.1 + 51,
            641
        ],
        [
            19*k3.1 + 3,
            641
        ],
        [
            23*k3.1 + 45,
            641
        ]
    ]
*], [* 665,
    [
        [
            7*k3.1 + 6,
            665
        ],
        [
            8*k3.1 + 3,
            665
        ]
    ]
*], [* 677,
    [
        [
            8*k3.1 + 15,
            677
        ]
    ]
*], [* 701,
    [
        [
            11*k3.1 + 9,
            701
        ]
    ]
*], [* 713,
    [
        [
            19*k3.1 + 3,
            713
        ]
    ]
*], [* 737,
    [
        [
            7*k3.1 + 72,
            737
        ],
        [
            13*k3.1 + 66,
            737
        ],
        [
            16*k3.1 + 51,
            737
        ]
    ]
*], [* 761,
    [
        [
            k3.1 + 18,
            761
        ]
    ]
*], [* 785,
    [
        [
            19*k3.1 + 57,
            785
        ],
        [
            23*k3.1 + 9,
            785
        ]
    ]
*], [* 797,
    [
        [
            19*k3.1 + 33,
            797
        ],
        [
            22*k3.1 + 69,
            797
        ]
    ]
*], [* 857,
    [
        [
            5*k3.1 + 36,
            857
        ]
    ]
*], [* 881,
    [
        [
            8*k3.1 + 3,
            881
        ],
        [
            11*k3.1 + 9,
            881
        ],
        [
            11*k3.1 + 18,
            881
        ]
    ]
*], [* 905,
    [
        [
            8*k3.1 + 3,
            905
        ]
    ]
*], [* 929,
    [
        [
            23*k3.1 + 63,
            929
        ]
    ]
*], [* 953,
    [
        [
            11*k3.1 + 30,
            953
        ]
    ]
*], [* 965,
    [
        [
            k3.1 + 66,
            965
        ],
        [
            4*k3.1 + 51,
            965
        ],
        [
            5*k3.1 + 66,
            965
        ],
        [
            14*k3.1 + 39,
            965
        ],
        [
            17*k3.1 + 51,
            965
        ],
        [
            23*k3.1 + 30,
            965
        ]
    ]
*], [* 989,
    [
        [
            11*k3.1 + 9,
            989
        ]
    ]
*] ];






