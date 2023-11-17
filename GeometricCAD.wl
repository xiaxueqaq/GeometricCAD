(* ::Package:: *)

BeginPackage["GeometricCAD`"];


Needs["Singular`"];


DecomposeLocallyClosedSet::usage="Decompose A Locally Closed Set into Distinguished (Principal) Locally Closed Sets";


IdealContainment::usage="Test if I is contained in J";


Proj1::usage="Geometric Proj1";


Proj2::usage="Geometric Proj2";


CADVisualize2D::usage="A testing function";


EmptyVarietyQ::usage="Test if a variety is empty";


CADCellsSQF::usage="Get the squarefree part of the defining polynomials of cells";


CADCellDecompose::usage="A Heurstic, decompose the cells by factoring the defining polynomials of cells";


CADCellNormalize::usage="A canonical form of a distinguished locally closed set";


CADProjection::usage="Geometric CAD Projection";


CADAlternativeProjection::usage="Alternative Geometric CAD Projection";


CADRealAxisPolynomials::usage="Univariate Polynomials Defining Intervals and Points";


CADPartition1D::usage="CAD Partition the Real Axis";


CADLift::usage="CAD Lifting";


CADGeometricPartition1D::usage="CAD Partition the Real Axis";


CADGeometricLift::usage="Geometric Lifting";


GeometricCylindricalDecomposition::usage="Main Procedure of GeometricCAD";


GeometricCylindricalDecompositionEqs::usage="The GeometricCAD exploiting Equational Constraints";


TraceMap::usage="Trace of Multiplication Matrix";


Begin["`Private`"];


DecomposeLocallyClosedSet[f_,g_]:=Table[{Join[f,g[[1;;i-1]]],g[[i]]},{i,1,Length[g]}];


TraceMap[f_,GB_,x_,s_]:=Return[Simplify[Plus@@(Table[Coefficient[PolynomialReduce[x^i*f,GB,x][[2]],x,i],{i,0,s-1}])]];


PrimeDecomposition[f_,x_]:=Module[{rad},
	(*rad=SingularRadical[f,x];*)
	Return[SingularMinAssGTZ[f,x]];
]


IdealContainment[f_,g_,y_]:=Module[{GB},
	GB=GroebnerBasis[g,y,MonomialOrder->DegreeReverseLexicographic];
	Return[Length[Select[f,PolynomialReduce[#,GB,y,MonomialOrder-> DegreeReverseLexicographic][[2]]=!=0&]]==0]
];


Proj1[f_,g_,h_,y_,x_]:=Module[{MatMonoOrder,GB,JGB,IGB,ret,Js,w,s,H,H0,chi,lam,coefs},
	MatMonoOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[y]+4],{i,Length[y]+1},{j,Length[y]+1}];
	(*The Block Order x>grevlex(y); Notice that MatMonoOrder[[2,1]]=1, but it does not matter*)
	GB=GroebnerBasis[f,Join[{x},y],MonomialOrder->MatMonoOrder,Method->"GroebnerWalk"];
	If[GB=={1},Return[{{g,1}}]];
	(*GB=SingularGroebner[f,y,{x},MonomialOrder\[Rule]{DegreeReverseLexicographic,Lexicographic}];*)
	JGB=Select[GB,Exponent[#,x]==0&];
	IGB=Select[GB,Exponent[#,x]>0&];
	If[Not[IdealContainment[JGB,g,y]],
		ret=DecomposeLocallyClosedSet[g,JGB];
		(*Js=SingularMinAssGTZ[JGB, y];*)
		Js=PrimeDecomposition[JGB,y];
		Return[Join[ret,Join@@(Proj1[Join[#,f],#,h,y,x]&/@Js)]];
	];
	If[Length[IGB]==0,
		Return[Proj1[Append[f,h],g,1,y,x]]
	];
	w=Times@@(FactorList[Times@@(Coefficient[#,x,Exponent[#,x]]&/@IGB)][[1;;-1,1]]);
	s=Min@@(Exponent[#,x]&/@IGB);
	H0=Table[TraceMap[x^i*h,IGB,x,s],{i,0,2*s-2}];
	H=Table[H0[[i+j-1]],{i,s},{j,s}];
	chi=CharacteristicPolynomial[H,lam];
	coefs=Numerator[Together[#]]&/@CoefficientList[chi,lam];
	ret=Table[{Join[JGB,coefs[[1;;i]]],w*coefs[[i+1]]},{i,0,s}];
	(*Js=SingularMinAssGTZ[Append[JGB,w],y];*)
	Js=PrimeDecomposition[Append[JGB,w],y];
	Return[Join[ret,Join@@(Proj1[Join[#,f],#,h,y,x]&/@Js)]];
];


Proj2Sub[f_,g_,h_,w_,y_,x_]:=Module[{MatMonoOrder,GB,z,JGB,IGB,Js,wp,AF,ret},
	(*Print["Proj2Sub Called with f=",f,", g=",g,", h=",h,", w=",w];*)
	MatMonoOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,j-1,1]-KroneckerDelta[i,j,2]+KroneckerDelta[i,3]-KroneckerDelta[i+j,Length[y]+6],{i,Length[y]+2},{j,Length[y]+2}];
	(*grevlex(z,x)>grevlex(y)*)
	GB=GroebnerBasis[Join[f,{z*h-1}],Join[{z,x},y],MonomialOrder->MatMonoOrder,Method->"GroebnerWalk"];
	(*Print["Proj2Sub= ",GB];*)
	If[GB=={1},Return[{}]];
	JGB=Select[GB,((Exponent[#,x]==0)&&(Exponent[#,z]==0))&];
	IGB=Select[GB,((Exponent[#,x]>0)||(Exponent[#,z]>0))&];
	If[Not[IdealContainment[JGB,g,y]],
		(*Js=SingularMinAssGTZ[JGB,y];*)
		Js=PrimeDecomposition[JGB,y];
		Return[Join@@(Proj2Sub[Join[#,f],#,h,w,y,x]&/@Js)];
	];
	AF=First[MonomialList[#,{z,x},DegreeReverseLexicographic]]&;
	wp=Times@@(FactorList[Times@@(Divide[AF[#],x^Exponent[AF[#],x]*z^Exponent[AF[#],z]]&/@IGB)][[1;;-1,1]]);
	(*Print["wp=",wp];*)
	(*Js=SingularMinAssGTZ[Append[JGB,wp],y];*)
	Js=PrimeDecomposition[Append[JGB,wp],y];
	(*ret=Join[{{JGB,w*wp}},Join@@(Proj2Sub[Join[#,f],#,h,w,y,x]&/@Js)];
	Print["Proj2Sub f=",f,", g=",g,", h=",h," ,w=",w,"; Return=",ret];
	Return[ret];*)
	Return[Join[{{JGB,w*wp}},Join@@(Proj2Sub[Join[#,f],#,h,w,y,x]&/@Js)]];
];


Proj2[f_,ff_,g_,h_,hp_,y_,x_]:=Module[{GB,MatMonoOrder,JGB,IGB,Js,w,ret},
	If[f===ff,Return[{}]];
	MatMonoOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[y]+4],{i,Length[y]+1},{j,Length[y]+1}];
	GB=GroebnerBasis[f,Join[{x},y],MonomialOrder-> MatMonoOrder,Method->"GroebnerWalk"];
	(*Print["Proj2= ",GB];*)
	If[GB=={1},Return[{}]];
	JGB=Select[GB,Exponent[#,x]==0&];
	IGB=Select[GB,Exponent[#,x]>0&];
	If[Not[IdealContainment[JGB,g,y]],
		(*Js=SingularMinAssGTZ[JGB,y];*)
		Js=PrimeDecomposition[JGB,y];
		Return[Join@@(Proj2[Join[#,f],ff,#,h,hp,y,x]&/@Js)];
	];
	If[Length[IGB]==0,Return[Proj2[Append[f,h],ff,g,1,hp,y,x]]];
	w=Times@@(FactorList[Times@@(Coefficient[#,x,Exponent[#,x]]&/@IGB)][[1;;-1,1]]);
	(*Js=SingularMinAssGTZ[Append[JGB,w],y];*)
	Js=PrimeDecomposition[Append[JGB,w],y];
	(*ret=Join[Proj2Sub[Join[f,ff],{},h,w,y,x],Join@@(Proj2[Join[#,f],ff,#,h,y,x]&/@Js)];
	Print["Proj2 ret=",ret];
	Return[ret];*)
	Return[Join[Proj2Sub[Join[f,ff],{},hp,w,y,x],Join@@(Proj2[Join[#,f],ff,#,h,hp,y,x]&/@Js)]];
];


BalancedProj2[f_,ff_,g_,h_,hp_,y_,x_]:=Module[{mdeg1,mdeg2},
	mdeg1=Max@@(Exponent[#,x]&/@f);
	mdeg2=Max@@(Exponent[#,x]&/@ff);
	If[mdeg1<mdeg2,
		Return[Proj2[f,ff,g,h,hp,y,x]],
		Return[Proj2[ff,f,g,hp,h,y,x]]
	];
]


EmptyVarietyQ[V_,h_,x_]:=Module[{z,tmp,MatMonoOrder},
	(*If[Length[V]\[Equal]0,Return[True]];*)
	If[(h==0)||MemberQ[V,1],Return[True]];
	If[Length[x]==1,
		If[Length[V]==0,Return[Exponent[h,x]==0]];
		tmp=PolynomialGCD@@V;
		If[tmp-PolynomialGCD[tmp,h]===0,
			Return[True],
			Return[False]
		];
	];
	tmp=GroebnerBasis[V,x,MonomialOrder->DegreeReverseLexicographic];
	If[tmp==={1},Return[True]];
	MatMonoOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[x]+4],{i,Length[x]+1},{j,Length[x]+1}];
	If[GroebnerBasis[Join[tmp,{z*h-1}],Join[{z},x],MonomialOrder->MatMonoOrder]==={1},
		Return[True],
		Return[False]
	];
]


CADCellsSQF[L_]:=Module[{},
Return[Table[{Table[Times@@(FactorSquareFreeList[L[[i,1,j]]][[All,1]]),{j,Length[L[[i,1]]]}],Times@@(FactorSquareFreeList[L[[i,2]]][[All,1]])},{i,Length[L]}]];
]


CADCellDecomposeAuxiliary[L_]:=Module[{factors,ret},
	factors={#}&/@(Select[FactorList[L[[1]]][[All,1]],Length[Variables[#]]>0&]);
	If[Length[L]==1,Return[factors]];
	ret=CADCellDecomposeAuxiliary[L[[2;;-1]]];
	Return[Join@@Outer[Join[#1,#2]&,factors,ret,1]];
]


CADCellDecompose[L_]:=Module[{Comps,tmp},
	tmp=Select[L[[1]],#=!=0&];
	If[Length[tmp]==0,Return[{L}]];
	If[Length[Variables[L[[1]]]]==1,tmp={PolynomialGCD@@L[[1]]}];
	Comps=CADCellDecomposeAuxiliary[tmp];
	Return[Table[{Comps[[i]],L[[2]]},{i,Length[Comps]}]];
]


CADCellNormalize[L_,x_]:=Module[{V,d,lc},
	V=GroebnerBasis[L[[1]],x,MonomialOrder->DegreeReverseLexicographic];
	If[Length[V]>0,
		(*If[Length[V]\[Equal]0,Print["WARNING!!!!! Groebner Basis is EMPTY!!!!! scheiss",L]];*)
		If[Length[x]==1,V[[1]]=Times@@(FactorList[V[[1]]][[1;;-1,1]])];
		d=PolynomialReduce[L[[2]],V,x,MonomialOrder->DegreeReverseLexicographic][[2]];
		If[d===0,Return[{{1},1}]];
		If[EmptyVarietyQ[V,d,x],Return[{{1},1}]];
		If[Length[x]==1,V[[1]]=PolynomialQuotient[V[[1]],PolynomialGCD[V[[1]],d],x[[1]]];Return[{V,1}]];
		lc=First[Values[CoefficientRules[d,x,DegreeReverseLexicographic]]];
		Return[{V,Expand[d/lc]}],
		If[L[[2]]===0,Return[{{1},1}]];
		If[Length[x]==1,Return[{{},Times@@FactorList[L[[2]]][[1;;-1,1]]}]];
		lc=First[Values[CoefficientRules[L[[2]],x,DegreeReverseLexicographic]]];
		Return[{{},Expand[L[[2]]/lc]}]
	]
]


CADProjection[L_,x_,dec_:True]:=Module[{i,j,ret1,ret2,cells},
	If[Length[x]==1,Return[]];
	If[dec,
		ret1=Join@@CADCellDecompose/@CADCellsSQF[Join@@Monitor[Table[Proj1[L[[i,1]],{},L[[i,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]}],ProgressIndicator[i,{1,Length[L]}]]];
		ret2=Join@@CADCellDecompose/@CADCellsSQF[Join@@Join@@Monitor[Table[Proj2[L[[i,1]],L[[j,1]],{},L[[i,2]],L[[j,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]},{j,i-1}],ProgressIndicator[(i-2)*(i-1)/2+j,{1,Length[L]*(Length[L]-1)/2},BaseStyle-> ControlsRendering -> "Generic"]]];
		,
		ret1=CADCellsSQF[Join@@Monitor[Table[Proj1[L[[i,1]],{},L[[i,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]}],i]];
		ret2=CADCellsSQF[Join@@Join@@Monitor[Table[Proj2[L[[i,1]],L[[j,1]],{},L[[i,2]],L[[j,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]},{j,i-1}],(i-2)*(i-1)/2+j]];
		];
	Print["ret1=",ret1];
	Print["ret2=",ret2];
	(*cells=Reverse[DeleteDuplicates[Join[Select[ret1,(!EmptyVarietyQ[#[[1]],#[[2]],x[[1;;-2]]])&&(Length[#[[1]]]>0)&],
			   Select[ret2,!EmptyVarietyQ[#[[1]],#[[2]],x[[1;;-2]]]&]]]];*)
	cells=Reverse[Select[DeleteDuplicates[CADCellsSQF[CADCellNormalize[#,x[[1;;-2]]]&/@(Join[Select[ret1,Length[#[[1]]]>0&],ret2])]],#[[1]]=!={1}&]];
	If[dec,
		cells=Join@@CADCellDecompose/@cells;
	];
	Print["cells=",cells];
	(*CADProjection[cells,x[[1;;-2]]];*)
	Return[cells];
]


CADPreprocess1D[L_,x_]:=Module[{polygcd},
	If[Length[L[[1]]]==0,
		If[L[[2]]===0,Return[1],Return[L[[2]]]],
		polygcd=PolynomialGCD@@Append[L[[1]],Extension->Automatic];
		If[polygcd===0,If[L[[2]]===0,Return[1],Return[L[[2]]]]];
		Return[PolynomialQuotient[polygcd,PolynomialGCD[polygcd,L[[2]],Extension->Automatic],x]]
	]
]


CADRealAxisPolynomials[L_,x_]:=Module[{},
	Return[DeleteDuplicates[Join@@Table[FactorList[#,Extension->Automatic][[All,1]]&[CADPreprocess1D[L[[i]],x]],{i,1,Length[L]}]]];
]


CADPartition1D[L_,x_]:=Module[{polys,V,cp},
	polys=CADRealAxisPolynomials[L,x];
	V=Times@@polys; V=PolynomialQuotient[V,PolynomialGCD[V,D[V,x],Extension->Automatic],x];
	cp=Solve[V==0,x,Reals];
	If[Length[cp]>0,
		cp=Sort[x/.cp,Less];
		Return[Riffle[Join[{Rationalize[cp[[1]]-1,1/2]},
			Table[Rationalize[(cp[[i]]+cp[[i+1]])/2,(cp[[i+1]]-cp[[i]])/4],{i,Length[cp]-1}],
			{Rationalize[cp[[Length[cp]]]+1,1/2]}],cp]],
		Return[{0}]
	];
]


CADLift[L_,x_,Silhouette_]:=Module[{},
	Return[Join@@Table[Append[Silhouette[[i]],#]&/@CADPartition1D[L/.Table[x[[j]]-> Silhouette[[i,j]],{j,Length[x]-1}],x[[-1]]],{i,Length[Silhouette]}]];
]


CADGeometricPartition1D[L_,x_]:=Module[{i,flag,V,d,polygcd,cp,intv},
	flag=False;
	V=1;
	d=1;
	For[i=1,i<= Length[L],i++,
		If[Length[L[[i,1]]]==0,
			flag=True;If[L[[i,2]]===0,Continue[],d=d*L[[i,2]];Continue[]],
			polygcd=PolynomialGCD@@Append[L[[i,1]],Extension->Automatic];
			If[polygcd===0,flag=True;If[L[[i,2]]===0,Continue[],d=d*L[[i,2]];Continue[]]];
			V=V*PolynomialQuotient[polygcd,PolynomialGCD[polygcd,L[[i,2]],Extension->Automatic],x];
		]
	];
	V=PolynomialQuotient[V,PolynomialGCD[V,D[V,x],Extension->Automatic],x];
	d=PolynomialQuotient[d,PolynomialGCD[d,D[d,x],Extension->Automatic],x];
	d=PolynomialQuotient[d,PolynomialGCD[V,d,Extension->Automatic],x];
	If[flag,
		cp=Solve[d*V==0,x,Reals];
		If[Length[cp]>0,
			cp=Sort[x/.cp,Less];
			intv=Join[{Rationalize[cp[[1]]-1,1/2]},
			Table[Rationalize[(cp[[i]]+cp[[i+1]])/2,(cp[[i+1]]-cp[[i]])/4],{i,Length[cp]-1}],
			{Rationalize[cp[[Length[cp]]]+1,1/2]}];
			cp=Solve[V==0,x,Reals];
			If[Length[cp]==0,Return[intv],cp=Sort[x/.cp,Less];Return[Sort[Join[cp,intv],Less]]]
		,
			Return[{0}];
		]
	,
		cp=Solve[V==0,x,Reals];
		If[Length[cp]>0,
			cp=Sort[x/.cp,Less]; Return[cp],
			Return[{}]
		]
	]
]


CADGeometricLift[L_,x_,Silhouette_]:=Module[{},
	Return[Join@@Table[Append[Silhouette[[i]],#]&/@CADGeometricPartition1D[L/.Table[x[[j]]-> Silhouette[[i,j]],{j,Length[x]-1}],x[[-1]]],{i,Length[Silhouette]}]];
]


CADRecursiveProjection[L_,x_,dec_:True]:=Module[{ps},
	If[Length[x]==1,Return[{L}]];
	ps=CADProjection[L,x,dec];
	Return[AppendTo[CADRecursiveProjection[ps,x[[1;;-2]],dec],L]];
]


GeometricCylindricalDecomposition[L_,x_,dec_:True]:=Module[{cells,samples},
	cells=CADRecursiveProjection[L,x,dec];
	samples[1]:={#}&/@CADPartition1D[cells[[1]],x[[1]]];
	samples[n_]:=CADLift[cells[[n]],x[[1;;n]],samples[n-1]];
	Return[Table[samples[i],{i,Length[x]}]];
]


GeometricCylindricalDecompositionEqs[L_,eqs_,x_,dec_:True]:=Module[{cells,samples,lexGB,k,ret1,ret2,tmp,elim,toproj},
	lexGB=GroebnerBasis[eqs,Reverse[x]];
	Print["GB=",lexGB];
	toproj=Table[{Join[#[[1]],eqs],#[[2]]}&[L[[i]]],{i,Length[L]}];
	cells={Table[{Join[#[[1]],eqs],#[[2]]}&[L[[i]]],{i,Length[L]}]};
	For[k=Length[x]-1,k>=1,k--,
		elim=Select[lexGB,SubsetQ[x[[1;;k]],Variables[#]]&];
		
		(*We have to manually Proj here, because CADProjection is optimized to omit the open sets in Proj1*)
		If[dec,
		
		ret1=Join@@CADCellDecompose/@CADCellsSQF[Join@@Monitor[Table[Proj1[toproj[[i,1]],{},toproj[[i,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]}],ProgressIndicator[i,{1,Length[toproj]}]]];
		ret2=Join@@CADCellDecompose/@CADCellsSQF[Join@@Join@@Monitor[Table[BalancedProj2[toproj[[i,1]],toproj[[j,1]],{},toproj[[i,2]],toproj[[j,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]},{j,i-1}],{ProgressIndicator[(i-1)*(i-2)/2+j,{1,Length[toproj]*(Length[toproj]-1)/2},BaseStyle-> ControlsRendering -> "Generic"],i,j}]];
		(*ret1=Join@@CADCellDecompose/@CADCellsSQF[Join@@Table[Proj1[toproj[[i,1]],{},toproj[[i,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]}]];
		ret2=Join@@CADCellDecompose/@CADCellsSQF[Join@@Join@@Table[Proj2[toproj[[i,1]],toproj[[j,1]],{},toproj[[i,2]],toproj[[j,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]},{j,i-1}]];*)
		,
		ret1=CADCellsSQF[Join@@Table[Proj1[toproj[[i,1]],{},toproj[[i,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]}]];
		ret2=CADCellsSQF[Join@@Join@@Table[Proj2[toproj[[i,1]],toproj[[j,1]],{},toproj[[i,2]],toproj[[j,2]],x[[1;;k]],x[[k+1]]],{i,Length[toproj]},{j,i-1}]];
		];
		Print["ret1=",ret1];
		Print["ret2=",ret2];
		If[Length[elim]>0,
			ret1={Join[#[[1]],elim],#[[2]]}&/@ret1;
			ret2={Join[#[[1]],elim],#[[2]]}&/@ret2;
			tmp=Reverse[Select[DeleteDuplicates[CADCellNormalize[#,x[[1;;k]]]&/@(Join[ret1,ret2])],#[[1]]=!={1}&]];
			If[dec,tmp=Join@@CADCellDecompose/@tmp];
			toproj=tmp;
			PrependTo[cells,tmp],
			(*The Equational Constraints are exhausted*)
			ret1=CADCellNormalize[#,x[[1;;k]]]&/@ret1;
			ret2=CADCellNormalize[#,x[[1;;k]]]&/@ret2;
			If[dec,ret1=Join@@CADCellDecompose/@ret1;ret2=Join@@CADCellDecompose/@ret2;ret1=CADCellNormalize[#,x[[1;;k]]]&/@ret1;ret2=CADCellNormalize[#,x[[1;;k]]]&/@ret2;];
			tmp=Reverse[Select[DeleteDuplicates[Join[ret1,ret2]],#[[1]]=!={1}&]];
			PrependTo[cells,tmp];
			ret1=Select[ret1,Length[#[[1]]]>0&];
			toproj=Reverse[Select[DeleteDuplicates[Join[ret1,ret2]],#[[1]]=!={1}&]];
		];
		Print[tmp];
	];
	(*Return[cells];*)
	samples[1]:={#}&/@CADGeometricPartition1D[cells[[1]],x[[1]]];
	samples[n_]:=CADGeometricLift[cells[[n]],x[[1;;n]],samples[n-1]];
	Return[Table[samples[i],{i,Length[x]}]];
]


AlternativeProj2[f_,g_,h_,y_,x_]:=Module[{GB,IGB,JGB,MatMonoOrder,Js,w},
	MatMonoOrder=Table[KroneckerDelta[i,j,1]+KroneckerDelta[i,2]-KroneckerDelta[i+j,Length[y]+4],{i,Length[y]+1},{j,Length[y]+1}];
	GB=GroebnerBasis[f,Join[{x},y],MonomialOrder->MatMonoOrder];
	If[GB=={1},Return[{}]];
	JGB=Select[GB,Exponent[#,x]==0&];
	IGB=Select[GB,Exponent[#,x]>0&];
	If[Not[IdealContainment[JGB,g,y]],
		Js=SingularMinAssGTZ[JGB, y];
		Return[Join@@(AlternativeProj2[Join[#,f],#,h,y,x]&/@Js)];
	];
	If[Length[IGB]==0,Return[AlternativeProj2[Append[f,h],g,1,y,x]]];
	w=Times@@(Coefficient[#,x,Exponent[#,x]]&/@IGB);
	Js=SingularMinAssGTZ[Append[JGB,w],y];
	Return[Join[{{g,w}},Join@@(AlternativeProj2[Join[#,f],#,h,y,x]&/@Js)]];
]


CADAlternativeProjection[L_,x_]:=Module[{ret1,ret2,cells},
	If[Length[x]==1,Return[]];
	ret1=Join@@CADCellDecompose/@CADCellsSQF[Join@@Table[Proj1[L[[i,1]],{},L[[i,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]}]];
	ret2=Join@@CADCellDecompose/@CADCellsSQF[Join@@Join@@Table[AlternativeProj2[Join[L[[i,1]],L[[j,1]]],{},L[[i,2]]*L[[j,2]],x[[1;;-2]],x[[-1]]],{i,Length[L]},{j,Length[L]-1}]];
	Print["ret1=",ret1];
	Print["ret2=",ret2];
	cells=Reverse[DeleteDuplicates[Join[Select[ret1,(!EmptyVarietyQ[#[[1]],#[[2]],x[[1;;-2]]])&&(Length[#[[1]]]>0)&],
			   Select[ret2,!EmptyVarietyQ[#[[1]],#[[2]],x[[1;;-2]]]&]]]];
	Print["cells=",cells];
	(*CADAlternativeProjection[cells,x[[1;;-2]]];	*)
	Return[cells];
]


CADVisualize2D[L_,x_,pltBL_:{-2,-2},pltTR_:{2,2}]:=Module[{polys,plt},
	(*polys=Flatten[L];*)
	polys=Join@@L[[All,1]];
	plt=Table[ContourPlot[#==0,Element[x,Rectangle[pltBL,pltTR]],ContourStyle->{ColorData[55][Mod[i*59,13]+1]},PlotPoints->50]&[polys[[i]]],{i,Length[polys]}];
	Return[Show@@plt];
]


End[];


EndPackage[];
