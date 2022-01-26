(* ::Package:: *)

(* ::Input:: *)
(*ClearAll@"Global`*";*)


(* ::Input::Initialization:: *)
epsteinZetaInternal::usage="Internal function: epsteinZeta[s,a,c,d] computes the Epstein zeta function in the form sum_{n in Z^d} exp(2Pi c.(a n))/|a n - d|^s using the algorithm in Crandall, R., Unified algorithms for polylogarithm, L-series, and zeta variants. Algorithmic Reflections: Selected Works. PSIpress (2012).";
epsteinZetaInternal[s_,a_,c_,d_,maxL_:5,workPr_:60]:=Module[{sNum,aNum,cNum,dNum,dim,\[Gamma],aPrime,b,cPrime,dPrime,goA,goB,sumGrid,sumA,sumB,\[Zeta]},dim=Length@a;
{sNum,aNum,cNum,dNum}=N[{s,a,c,d},workPr];
(*We scale the Gramian of the bilinear form such that it has unit determinant*)
\[Gamma]=(Det@aNum)^(1/dim);
aPrime=aNum/\[Gamma];
b=Transpose@Inverse@aPrime;
(*Trim the phase shift c and the grid shift d so that they belong to the unit cell of the dual / primal grid*)
cPrime=Dot[b,FractionalPart[LinearSolve[b,\[Gamma] cNum]]];
dPrime=Dot[aPrime,FractionalPart[LinearSolve[aPrime,dNum/\[Gamma]]]];
(*Return values for the trivial zero of the Epstein zeta function and its pole at s\[Equal]d for c\[Equal]0*)
If[s==0,If[PossibleZeroQ@Norm[dNum],Return[-1],0]];
If[s==dim&&PossibleZeroQ@Norm[cNum],Return[ComplexInfinity]];
(*The computation of the Epstein zeta function uses two expoentially fast converging series, one over goA and the second over goB*)
goA[n_]:=goA[n]=Block[{nrmSqr,phase},nrmSqr=(aPrime . n-dPrime) . (aPrime . n-dPrime);
phase=cPrime . aPrime . n;
If[PossibleZeroQ@nrmSqr,0,Gamma[sNum/2,Pi nrmSqr]Exp[2Pi I phase]/(Pi nrmSqr)^(sNum/2)]];goB[k_]:=goB[k]=Block[{nrmSqr,phase},nrmSqr=(b . k-cPrime) . (b . k-cPrime);phase=dPrime . b . k;
If[PossibleZeroQ@nrmSqr,0,Gamma[(dim-sNum)/2,Pi nrmSqr]Exp[-2Pi I phase]/(Pi nrmSqr)^((dim-sNum)/2)]];
(*Helper function to sum the function go over the integer grid [-l, l]^dim*)
sumGrid[go_,l_]:=Block[{range,var},var=Array[Unique["x"],dim];range=Sequence@@Map[Flatten,Transpose@{var,ConstantArray[{-l,l},dim]}];N[Sum[go[var],Evaluate@range],workPr]];
sumA=sumGrid[goA,maxL];
sumB=sumGrid[goB,maxL];
\[Zeta]=0;
If[AllTrue[cPrime,PossibleZeroQ],\[Zeta]+=1/(sNum/2-dim/2)];
If[AllTrue[dPrime,PossibleZeroQ],\[Zeta]-=1/(sNum/2)];
\[Zeta]+=Exp[-I Pi cPrime . dPrime]sumA;
\[Zeta]+=Exp[I Pi cPrime . dPrime]sumB;
\[Zeta]*=Exp[I Pi cPrime . dPrime]Pi^(sNum/2)/Gamma[sNum/2];
\[Gamma]^(-sNum)Exp[2Pi I cPrime . (dNum/\[Gamma]-dPrime)]\[Zeta]
];

epsteinZetaStarInternal::usage="Internal function: epsteinZetaStar[s,a,c,d] computes the meromorphic continuation of sum_{n in Z^d} exp(2Pi c.(a n))/|a n - d|^s - exp(2Pi c.d) Fourier(|y|^(-\[Nu]))/V_Lambda using the algorithm in Crandall, R., Unified algorithms for polylogarithm, L-series, and zeta variants. Algorithmic Reflections: Selected Works. PSIpress (2012).";
epsteinZetaStarInternal[s_,a_,c_,d_,maxL_:5,workPr_:60]:=Module[{sNum,aNum,cNum,dNum,dim,\[Gamma],aPrime,b,cPrime,dPrime,goA,goB,sumGrid,sumA,sumB,\[Zeta]},dim=Length@a;
{sNum,aNum,cNum,dNum}=N[{s,a,c,d},workPr];
(*We scale the Gramian of the bilinear form such that it has unit determinant*)
\[Gamma]=(Det@aNum)^(1/dim);
aPrime=aNum/\[Gamma];
b=Transpose@Inverse@aPrime;
(*Trim the phase shift c and the grid shift d so that they belong to the unit cell of the dual / primal grid*)
cPrime=Dot[b,FractionalPart[LinearSolve[b,\[Gamma] cNum]]];
dPrime=Dot[aPrime,FractionalPart[LinearSolve[aPrime,dNum/\[Gamma]]]];
(*Return values for the trivial zero of the Epstein zeta function and its pole at s\[Equal]d for c\[Equal]0*)
If[s==0,If[PossibleZeroQ@Norm[dNum],Return[-1],0]];
If[s==dim&&PossibleZeroQ@Norm[cNum],Return[ComplexInfinity]];
(*The computation of the Epstein zeta function uses two expoentially fast converging series, one over goA and the second over goB*)
goA[n_]:=goA[n]=Block[{nrmSqr,phase},nrmSqr=(aPrime . n-dPrime) . (aPrime . n-dPrime);
phase=cPrime . aPrime . n;
If[PossibleZeroQ@nrmSqr,0,Gamma[sNum/2,Pi nrmSqr]Exp[2Pi I phase]/(Pi nrmSqr)^(sNum/2)]];
goB[ConstantArray[0,dim]]=If[PossibleZeroQ@(cPrime . cPrime),0,(Gamma[(dim-sNum)/2,Pi cPrime . cPrime]-Gamma[(dim-sNum)/2])/(Pi cPrime . cPrime)^((dim-sNum)/2)];
goB[k_]:=goB[k]=Block[{nrmSqr,phase},nrmSqr=(b . k-cPrime) . (b . k-cPrime);phase=dPrime . b . k;
If[PossibleZeroQ@nrmSqr,0,Gamma[(dim-sNum)/2,Pi nrmSqr]Exp[-2Pi I phase]/(Pi nrmSqr)^((dim-sNum)/2)]];
(*Helper function to sum the function go over the integer grid [-l, l]^dim*)
sumGrid[go_,l_]:=Block[{range,var},var=Array[Unique["x"],dim];range=Sequence@@Map[Flatten,Transpose@{var,ConstantArray[{-l,l},dim]}];N[Sum[go[var],Evaluate@range],workPr]];
sumA=sumGrid[goA,maxL];
sumB=sumGrid[goB,maxL];
\[Zeta]=0;
If[AllTrue[cPrime,PossibleZeroQ],\[Zeta]+=1/(sNum/2-dim/2)];
If[AllTrue[dPrime,PossibleZeroQ],\[Zeta]-=1/(sNum/2)];
\[Zeta]+=Exp[-I Pi cPrime . dPrime]sumA;
\[Zeta]+=Exp[I Pi cPrime . dPrime]sumB;
\[Zeta]*=Exp[I Pi cPrime . dPrime]Pi^(sNum/2)/Gamma[sNum/2];
\[Gamma]^(-sNum)Exp[2Pi I cPrime . (dNum/\[Gamma]-dPrime)]\[Zeta]
];

epsteinZeta::usage="epsteinZetaReg[\[Nu],A,x,y] computes the Epstein zeta function sum_{z in Lambda} exp(- 2 Pi I y.(z - x))/|z - x|^\[Nu] using the algorithm in Crandall, R., Unified algorithms for polylogarithm, L-series, and zeta variants. Algorithmic Reflections: Selected Works. PSIpress (2012).";
epsteinZeta[\[Nu]_,A_,x_,y_,maxL_:5,workPr_:60]:=epsteinZetaInternal[\[Nu],A,-y,x,maxL,workPr];

epsteinZetaReg::usage="epsteinZetaReg[\[Nu],A,x,y] computes the regularised Epstein zeta function sum_{z in Lambda} exp(- 2 Pi I y.(z - x))/|z - x|^\[Nu] - Fourier(|y|^(-\[Nu]))/V_Lambda using the algorithm in Crandall, R., Unified algorithms for polylogarithm, L-series, and zeta variants. Algorithmic Reflections: Selected Works. PSIpress (2012).";
epsteinZetaReg[\[Nu]_,A_,x_,y_,maxL_:5,workPr_:60]:=Exp[2Pi*I*x . y]epsteinZetaStarInternal[\[Nu],A,-y,x,maxL,workPr];
