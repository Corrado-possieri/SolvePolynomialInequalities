-- -*- coding: utf-8 -*-
-- solvePackage.m2
-- Copyright (C) 2017  Laura Menini, Corrado Possieri, Antonio Tornambe

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 3 of the License, or (at
--  your option) any later version.
--
--  This program is distributed in the hope that it will be useful, but
--  WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  General Public License for more details.
--
--  You should have received a copy of the GNU General Public License along
--  with this program; if not, see <http://www.gnu.org/licenses/>.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newPackage (
 "DisSolve",
 Version => "1.0",
 Date => "May 18, 2017",
 Headline => "A package to solve systems of polynomial inequalities",
 Authors => {
  {Name => "Laura Menini", Email => "menini@disp.uniroma2.it"},
  {Name => "Corrado Possieri", Email => "possieri@ing.uniroma2.it"},
  {Name => "Antonio Tornambe", Email => "tornambe@disp.uniroma2.it"}
 }
)

-- add here local path to NumericSolutions package
needsPackage("NumericSolutions",FileName => "~/Documents/M2pack/Def/NumericSolutions.m2");

export {
 "solveInequalities",
 -- options
 "Toll"
}

solveInequalities = method(TypicalValue => List, Options => {Toll => 10.^-3})
solveInequalities(List, List, List) := opts -> (nonstrict,strict,diseq) -> (
 -- compute the solution to a system of polynomial inequalities.
 
 -- inputs: the non-strinct inequalties nonstrict;
 --         the strinct inequalties strict;
 --         the inequalties diseq.
 
 -- output: a set of solutions.
 
 -- define the tolerance
 toll := opts.Toll;
 
 
 -- get parameters from the data
 s := length nonstrict;
 m := length strict;
 l := length diseq;
 
 R := QQ;
 Rvars := {};
 n := 0;
 coeR := QQ;
 if s != 0 then (
  R = ring nonstrict#0;
  Rvars = gens R;
  n = length Rvars;
  coeR = coefficientRing R;
 ) else if m != 0 then (
  R = ring strict#0;
  Rvars = gens R;
  n = length Rvars;
  coeR = coefficientRing R;
 ) else if l != 0 then (
  print "c";
  R = ring diseq#0;
  Rvars = gens R;
  n = length Rvars;
  coeR = coefficientRing R;
 ) else (
  error "no system has been given"
 );

 
 -- define auxiliary symbols
 v := getSymbol "v";
 w := getSymbol "w";
 u := getSymbol "u";
 
 k := getSymbol "k";
 z := getSymbol "z";
 y := getSymbol "y";
 
 lnx := length Rvars;
 
 vvars := new List from v_1..v_s;
 lnv := lnx + length vvars;

 wvars := new List from w_1..w_m;
 lnw := lnv + length wvars; 
 
 uvars := new List from u_1..u_l;
 lnu := lnw + length uvars;
 
 kvars := new List from k_1..k_s;
 lnk := lnu + length kvars;
 
 zvars := new List from z_1..z_m;
 lnz := lnk + length zvars;
 
 yvars := new List from y_1..y_l;
 lny := lnz + length yvars;
 
 -- define the new ring
 S := coeR[Rvars | vvars | wvars | uvars | kvars | zvars | yvars];
 svars := gens S;
 
 -- print svars;
 
 nxvars := new List from  (svars#0)..(svars#(lnx-1));
 if lnx != lnv then (
  nvvars := new List from  (svars#lnx)..(svars#(lnv-1));
 );
 if lnv != lnw then (
 nwvars := new List from  (svars#lnv)..(svars#(lnw-1));
 );
 if lnw != lnu then (
  nuvars := new List from  (svars#lnw)..(svars#(lnu-1));
 );
 if lnu != lnk then ( 
  nkvars := new List from  (svars#lnu)..(svars#(lnk-1));
 );
 if lnk != lnz then (
  nzvars := new List from  (svars#lnk)..(svars#(lnz-1));
 );
 if lnz != lny then (
  nyvars := new List from  (svars#lnz)..(svars#(lny-1));
 );
 
 
 -- define the polynomial J
 J := substitute(0,S);
 for jj from 0 to n - 1 do (
  J = J + substitute(random(QQ),S)*(nxvars#(jj) - substitute(random(QQ),S))^2;
 );
 for jj from 0 to s - 1 do (
  J = J + substitute(random(QQ),S)*(nvvars#(jj) - substitute(random(QQ),S))^2
      + nkvars#(jj) * (substitute(nonstrict#jj,S) - (nvvars#(jj))^2);
 );
 for jj from 0 to m - 1 do (
  J = J + substitute(random(QQ),S)*(nwvars#(jj) - substitute(random(QQ),S))^2
      + nzvars#(jj) * (substitute(strict#jj,S)*(nwvars#(jj))^2 - 1);
 );
 for jj from 0 to l - 1 do (
  J = J + substitute(random(QQ),S)*(nuvars#(jj) - substitute(random(QQ),S))^2
      + nyvars#(jj) * (substitute(diseq#jj,S)*(nuvars#(jj)) - 1);
 );
 
 -- compute the gradient ideal I
 I := new MutableList;
 count := 0;
 for jj from 0 to length svars - 1 do (
  I#count = diff(svars#jj, J);
  count = count + 1;
 );
 I = new List from I;
 I = ideal(I);
 -- print transpose gens I;
 
 sols := solveSystem(I, Tolerance => toRR toll);
 
 -- print sols;
 
 -- get the elements from the Tally
 sols = elements(sols);
 
 -- keep only real solutions
 rsol := {};
 for ii from 0 to length sols - 1 do (
  isRealValue := true;
  for jj from 0 to n - 1 do (
   if isReal((sols#ii)#jj) == false then (
    isRealValue = false;
   );
  );
  if isRealValue then (
   psol := new MutableList;
   for jj from 0 to n - 1 do (
    psol#jj = ((sols#ii)#jj);
   );
   psol = new List from psol;
   -- print psol;
   rsol = append(rsol,psol);
  );
 );
 
 rsol
)

-- End of source code --

-------------------
-- Documentation
-------------------
beginDocumentation()

document { 
 Key => DisSolve,
 Headline => "A package to solve systems of polynomial inequalities",
 EM "DisSolve", " is a package for solving systems of polynomial inequalities.
 It requires a procedure to compute the set of all the solutions to a
 system of polynomial equalities, as the ones given in the package NumericSolutions."
} 

document {
 Key => {solveInequalities,(solveInequalities,List,List,List),
         [solveInequalities, Toll]},
 Headline => "script to compute a set of solutions to a system of inequalities",
 Usage => "solveInequalities(nonstrict,strict,diseq)",
 Inputs => {
  "nonstrict" => { "polynomials that need to be nonnegative."},
  "strict" => { "polynomials that need to be positive."} ,
  "diseq" => {"polynomials that need to be different from zero."},
  Toll => {"numerical tolerance."}
 },
 Outputs => {
  "sol" => {"set of real points that satisfy the inequalities."}
 },
 EXAMPLE lines ///
  R = QQ[x_1,x_2];
  ss = x_1^2+x_2^2-1;
  ns = x_1^2-1;
  di = x_1-2;
  sol = solveInequalities({ss},{ns},{di})
 ///
}    

end

