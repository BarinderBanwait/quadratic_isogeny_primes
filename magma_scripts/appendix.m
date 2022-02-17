/* appendix.m
    Magma code related to the appendix of the paper, written jointly with
    Maarten Derickx.

    ====================================================================

    This file is part of Quadratic Isogeny Primes.

    Copyright (C) 2022 Barinder Singh Banwait

    Quadratic Isogeny Primes is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

    The author can be reached at: barinder.s.banwait@gmail.com

    ====================================================================

*/

/*
    The following code carries out the check on torsion of the minus part of
    J_0(79), and is referenced in Lemma A.3.
*/

for p in PrimesUpTo(6) do;
  FF := GF(p^2);
  print FF;
  A2 := AffineSpace(FF,2);
  X0 := ModularCurve(A2,"Atkin",79);
  //time Invariants(ClassGroup(X0));
  //the above gives an error because magma
  //does not seem to realise that a modular curve
  //is actually a curve, so we go trough some hassle
  //to actually make a curve for which we can call
  //the class group function
  X0 := ProjectiveClosure(X0);
  dps := DefiningPolynomials(X0);
  R := Parent(dps[1]);
  P := ProjectiveSpace(R);
  X0 := Curve(P,dps);
  time Invariants(ClassGroup(X0));
end for;

/*
    The following code carries out the check on torsion of the minus part of
    J_0(53), and is referenced in the proof of Theorem 1.10.
*/

for p in PrimesUpTo(6) do;
  FF := GF(p^2);
  print FF;
  A2 := AffineSpace(FF,2);
  X0 := ModularCurve(A2,"Atkin",53);
  X0 := ProjectiveClosure(X0);
  dps := DefiningPolynomials(X0);
  R := Parent(dps[1]);
  P := ProjectiveSpace(R);
  X0 := Curve(P,dps);
  time Invariants(ClassGroup(X0));
end for;

/*
    The following code carries out the check on the rank of the minus part of
    J_0(53) over Qsqrt7, and is referenced in the proof of Theorem 1.10.
*/

p := 53;
Chi := KroneckerCharacter(28, Rationals());
ML := ModularSymbols(p,2);
tw := TwistedWindingElement(ML,1,Chi);

CL := CuspidalSubspace(ML);
minus_space := NewformDecomposition(CL)[2];
TL := AtkinLehner(minus_space,p);
assert TL + 1 eq 0; // sanity check that TL is the minus space
my_map := RationalMapping(minus_space);
twmap := my_map(tw); // non-zero, so rank of twist is zero
twmap; // non-zero, so rank of twist is zero