(* ::Package:: *)

(* ::Text:: *)
(*Copyright (c) 2016, Mohammad Deni Akbar, Yoshihiro Mizoguchi, Kyushu University*)
(**)
(*Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell*)
(*copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:*)
(*The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.*)
(*THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.*)


(* ::Text:: *)
(*Last Modified:2016/07/04*)
(*Created: 2014/07/22*)


(* ::Subsection:: *)
(*1. Strict Relation*)


(* ::Subsubsection:: *)
(*Basic Notation, and Operation*)


AllPairs[AllData_]:=Flatten[Table[{AllData[[i]],AllData[[j]]},
	{i,1,Length[AllData]},{j,1,Length[AllData]}],1];
not[A_, Y_] := Complement[A, Y]; 
(*Complemet of set of attribute Y from complete set of attribute A*)
RelComp[x_,y_]:=Module[{p},p=Intersection[Map[{#[[1]][[1]],#[[2]][[2]]}&,
	Select[Flatten[Table[{x[[i]],y[[j]]},{i,1,Length[x]},
	{j,1,Length[y]}],1],#[[1]][[2]]==#[[2]][[1]]&]]]];
(*Compisiton of relation between element of set attribute x and element
 of set attribute y *)
RelInv[a_]:=Module[{b,c},b=Transpose[a];c={b[[2]],b[[1]]};Transpose[c]];
(*Invers of relation a, a is pair of element attribute *)
Id[a_]:=Map[{#,#}&,a];
(*Identity relation element of set a*)
r[a_]:=Id[a]
(*r[a]\[SubsetEqual] Id[a]*)
SubsetQi[a_,b_]:=Fold[And,True,Flatten[Table[MemberQ[b,a[[i]]],
	{i,1,Length[a]}]]];
(*to confirm that every element of set a is subset of set b*)
DBProduct[a_,b_]:=Map[Flatten,Flatten[Table[{a[[i]],b[[j]]},
	{i,1,Length[a]},{j,1,Length[b]}],1]];
(*Cartesian product between element of set attribute a and element of set attribute b *)
DBProduct[l_]:=If[l=={},l,If[Length[l]==1,DB[First[l]],If[Length[l]==2,
	DBProduct[DB[First[l]],DB[First[Rest[l]]]],DBProduct[DB[First[l]],
	DBProduct[Rest[l]]]]]];
(*Cartesian product of collection attribute l, element of l is attibute of database*)
Idx[x_,a_]:=Module[{p},p=Position[x,a];p[[1]][[1]]];
(*Position an attribute a in set of attribute x*)
RhoXa[x_,a_]:=Map[If[AtomQ[#],{#,#},{#,#[[ Idx[x,a] ]]}]&,DBProduct[x]];
Intersections[l_]:=If[l=={},{},If[Length[l]==1,l[[1]],If[Length[l]==2,
	Intersection[First[l],First[Rest[l]]],
	Intersection[First[l],Intersections[Rest[l]]]]]];
(*Pair of projection element of set attribute x to an attribute a, a\[SubsetEqual]x*)
Unions[l_]:=If[l=={},{},If[Length[l]==1,l[[1]],If[Length[l]==2,
	Union[First[l],First[Rest[l]]],
	Union[First[l],Unions[Rest[l]]]]]];
Rho[x_,y_]:=Intersections[Map[RelComp[RhoXa[x,#],RelInv[RhoXa[y,#]]]&,y]];
(*Pair of projection element of set attribute x to element of set attribute y, 
such that y\[SubsetEqual]x*)
Theta[A_,x_]:=If[x=={},AllPairs[DBProduct[A]],Intersections[Map[
	RelComp[RhoXa[A,#],RelInv[RhoXa[A,#]]]&,x]]];
(*Pairs of equivalence relation set of attribute x from complete set of attribute A, with condition x\[SubsetEqual]A*)
IdD[x_]:=Intersections[Map[RelComp[RhoXa[x,#],RelInv[RhoXa[x,#]]]&,x]];
(*Identity relation, pair elements of set attribute x*)
r[f_]:=Table[If[f[[i]][[1]]==f[[i]][[2]],f[[i]][[1]],f],{i,Length[f]}];
(*single set from pairs of  identity set f*)


(* ::Subsubsection:: *)
(*2. Operation Database*)


DBProjection[A_,y_]:=Intersection[RelComp[RelInv[Rho[A,y]],
	RelComp[Id[DBProduct[A]],Rho[A,y]]],Id[DBProduct[y]]];
DBProjection[A_,rdb_,y_]:=Intersection[RelComp[RelInv[Rho[A,y]],
	RelComp[Id[rdb],Rho[A,y]]],Id[DBProduct[y]]];
DBProjection2[A_,rdb_,y_]:=RelComp[RelInv[Rho[A,y]],
	RelComp[Id[rdb],Rho[A,y]]]
(*DBProjection2[A_,y_,rdb_]:=RelComp[RelComp[RelInv[Rho[A,y]],Id[rdb]],Rho[A,y]];*)
(*Projection of relation database rdb with attributes A to attributes y, such that y\[SubsetEqual]A*)
NaturalJoin[x_,y_,r1_,r2_]:=Module[{XY,a,b,z},XY=Union[x,y];a=Rho[XY,x];b=Rho[XY,y];
z=Id[DBProduct[XY]];RelComp[Intersection[RelComp[a,
	RelComp[Id[r1],RelInv[a]]],z],
	Intersection[RelComp[b,RelComp[Id[r2],RelInv[b]]],
	z]]];
(*Join relation between relation database r1 with attributes x and 
relation database r2 with attributes y*)
DBSelection[A_,r_,{a_}<b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],#[[1]]<b&],Id[r]]],Id[r]];
DBSelection[A_,r_,{a_}<=b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],#[[1]]<=b&],Id[r]]],Id[r]];
DBSelection[A_,r_,{a_}==b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],#[[1]]==b&],Id[r]]],Id[r]];
DBSelection[A_,r_,{a_}>b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],#[[1]]>b&],Id[r]]],Id[r]];
DBSelection[A_,r_,{a_}>=b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],#[[1]]>=b&],Id[r]]],Id[r]];
DBSelection[A_,r_,c_>={a_}\[Or]{a_}>=b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],c>=#[[1]]\[Or]#[[1]]>=b&],Id[r]]],Id[r]];
DBSelection[A_,r_,c_>={a_}\[Or]{a_}>b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],c>=#[[1]]\[DoubleLeftRightArrow]#[[1]]>b&],Id[r]]],Id[r]];
DBSelection[A_,r_,c_>{a_}\[Or]{a_}>=b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],c>#[[1]]\[DoubleLeftRightArrow]#[[1]]>=b&],Id[r]]],Id[r]];
DBSelection[A_,r_,c_<{a_}\[Or]{a_}<b_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],c<#[[1]]\[Or]#[[1]]<b&],Id[r]]],Id[r]];
DBSelection[A_,r_,b_<={a_}<=c_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],b<=#[[1]]<=c&],Id[r]]],Id[r]];
DBSelection[A_,r_,b_<{a_}<=c_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],b<#[[1]]<=c&],Id[r]]],Id[r]];
DBSelection[A_,r_,b_<={a_}<c_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],b<=#[[1]]<c&],Id[r]]],Id[r]];
DBSelection[A_,r_,b_<{a_}<c_]:=Intersection[RelComp[Rho[A,{a}],
	RelComp[Select[RelInv[Rho[A,{a}]],b<#[[1]]<c&],Id[r]]],Id[r]];
(*Selection of relation database r with attribute A, with some condition in
 attribute a, for example a<b,a>b, etc. b and c is value that we want*)






up:o@l-of7r66999mmmm9immmmxzzzzz\[Yen]



(* ::Subsection:: *)
(*2. Fuzzy Relation.*)


(* ::Subsubsection:: *)
(*Basic Fuzzy Notations*)


FuzzyRelComp[x_,y_]:=FuzzyUnion[Map[{#[[1]][[1]],#[[2]][[2]],Min[#[[1]][[3]],#[[2]][[3]]]}&,
Select[Flatten[Table[{x[[i]],y[[j]]},{i,1,Length[x]},
	{j,1,Length[y]}],1],#[[1]][[2]]==#[[2]][[1]]&]]];
(*Compisiton of fuzzy relation between element of fuzzy set attribute x and element
 of fuzzy set attribute y *)
FuzzyId[a_]:=Map[{Drop[#,-1],Drop[#,-1],Last[#]}&,a];
(*Identity fuzzy relation element of fuzzy set a*)
ToFuzzy[r_]:=Map[Append[#,1.0]&,r];
(*To give fuzzy value of set r*)
FuzzyRho[x_,y_]:=ToFuzzy[Intersections[Map[RelComp[RhoXa[x,#],RelInv[RhoXa[y,#]]]&,y]]];
(*Pair of projection element of set attribute x to element of set attribute y with
fuzzy value in every pair,such that y\[SubsetEqual]x*)
FuzzyTheta[A_,x_]:=ToFuzzy[Theta[A,x]];
FuzzyRelInv[a_]:=Module[{b,c},b=Transpose[a];c={b[[2]],b[[1]],b[[3]]};Transpose[c]];
(*Invers of fuzzy relation a, a is pair of element attribute with fuzzy value *)
Fval[fr_,x_]:=Max[{0}~Join~Map[Last,Select[fr,Drop[#,-1]==x&]]];
FuzzyIntersection[x_,y_]:=Select[Module[{xx,yy},xx=Map[{Drop[#,-1],Last[#]}&,x];
Map[Append[#[[1]],Min[#[[2]],Fval[y,#[[1]]]]]&,xx]],Last[#]!=0&];
(*Intersection between fuzzy set x and fuzzy set y*)
FuzzyIntersection[d_]:=Module[{l},l=Intersection[Table[Select[d,Drop[#,-1]==Drop[d[[i]],-1]&],
	{i,Length[d]}]];
	Table[If[Length[l[[i]]]!=1,Flatten[{Drop[l[[i,1]],-1],Min[Table[Last[l[[i,k]]],
	{k,Length[l[[i]]]}]]},1],Flatten[l[[i]],1]],{i,Length[l]}]];
(*Intersection between set of fuzzy set l*)
FuzzyUnion[d_]:=Module[{l},l=Intersection[Table[Select[d,Drop[#,-1]==Drop[d[[i]],-1]&],
	{i,Length[d]}]];
	Table[If[Length[l[[i]]]!=1,Flatten[{Drop[l[[i,1]],-1],Max[Table[Last[l[[i,k]]],
	{k,Length[l[[i]]]}]]},1],Flatten[l[[i]],1]],{i,Length[l]}]];
(*Union between fuzzy set of fuzzy set d*)
FuzzyUnion[x_,y_]:=Select[Module[{xx,yy},xx=Map[{Drop[#,-1],Last[#]}&,x];
Map[Append[#[[1]],Max[#[[2]],Fval[y,#[[1]]]]]&,xx]],Last[#]!=0&];
(*Union between fuzzy set x and fuzzy set y*)
FuzzyUnion2[x_,y_]:=FuzzyUnion[Flatten[{x,y},1]];


(* ::Subsection:: *)
(*Fuzzy Operations*)


FuzzySelection[A_,r_,{a_}<b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],#[[1]]<b&],r]],r];
FuzzySelection[A_,r_,{a_}>b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],#[[1]]>b&],r]],r];
FuzzySelection[A_,r_,{a_}==b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],#[[1]]==b&],r]],r];
FuzzySelection[A_,r_,{a_}<=b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],#[[1]]<=b&],r]],r];
FuzzySelection[A_,r_,{a_}>=b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],#[[1]]>=b&],r]],r];
FuzzySelection[A_,r_,c_>={a_}\[Or]{a_}>=b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],c>=#[[1]]\[Or]#[[1]]>=b&],r]],r];
FuzzySelection[A_,r_,c_>{a_}\[Or]{a_}>=b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],c>#[[1]]\[Or]#[[1]]>=b&],r]],r];
FuzzySelection[A_,r_,c_>={a_}\[Or]{a_}>b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],c>=#[[1]]\[Or]#[[1]]>b&],r]],r];
FuzzySelection[A_,r_,c_>{a_}\[Or]{a_}>b_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],c>#[[1]]\[Or]#[[1]]>b&],r]],r];
FuzzySelection[A_,r_,b_<={a_}<=c_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],b<=#[[1]]<=c&],r]],r];
FuzzySelection[A_,r_,b_<{a_}<=c_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],b<#[[1]]<=c&],r]],r];
FuzzySelection[A_,r_,b_<={a_}<c_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],b<=#[[1]]<c&],r]],r];
FuzzySelection[A_,r_,b_<{a_}<c_]:=FuzzyIntersection[FuzzyRelComp[FuzzyRho[A,{a}],
	FuzzyRelComp[Select[FuzzyRelInv[FuzzyRho[A,{a}]],b<#[[1]]<c&],r]],r];
(*Selection of fuzzy relation database r with attribute A, with some condition in
 attribute a, for example a<b,a>b, etc. b and c is value that we want*)
FuzzyProjection[A_,rdb_,y_]:=FuzzyUnion[FuzzyRelComp[FuzzyRelComp[FuzzyRelInv[FuzzyRho[A,y]],rdb],FuzzyRho[A,y]]];
(*Projection of fuzzy relation database rdb with attributes A to attributes y, such that y\[SubsetEqual]A*)
FuzzyNaturalJoin[x_,y_,r1_,r2_]:=Module[{XY},XY=Union[x,y];
FuzzyRelComp[FuzzyIntersection[FuzzyRelComp[FuzzyRho[XY,x],
	FuzzyRelComp[r1,FuzzyRelInv[FuzzyRho[XY,x]]]],FuzzyId[ToFuzzy[DBProduct[XY]]]],
	FuzzyIntersection[FuzzyRelComp[FuzzyRho[XY,y],FuzzyRelComp[r2,FuzzyRelInv[FuzzyRho[XY,y]]]],
	FuzzyId[ToFuzzy[DBProduct[XY]]]]]];
(*Join relation between fuzzy relation database r1 with attributes x and 
fuzzy relation database r2 with attributes y*)


Fuzzyr[f_]:=Table[If[f[[i]][[1]]==f[[i]][[2]],Flatten[{f[[i]][[1]],f[[i]][[3]]},1],f],{i,Length[f]}];
fo[{XPosition_,X_},{APosition_,P_},{a1_,r1_},{a2_,r2_},{rule_,fr_,out_}]:=Module[{t,g},DB[XPosition]=Union[{X,80,100}];DB[APosition]={-100,P,90,120,190,280};t=FuzzyNaturalJoin[a1,a2,r1[X],r2[P]];g=FuzzyNaturalJoin[Union[a1,a2],rule,Fuzzyr[t],fr];Fuzzyr[FuzzyProjection[Union[a1,a2,rule],Fuzzyr[FuzzyRelComp[FuzzySelection[Union[a1,a2,rule],Fuzzyr[g],{XPosition}==X],FuzzySelection[Union[a1,a2,rule],Fuzzyr[g],{APosition}==P]]],{out}]]];
fo[x_,y_]:=fo[{XPosition,x},{APosition,y},{PT,rPT},{AT,rAT},{IT,rSteer,Steer}];
