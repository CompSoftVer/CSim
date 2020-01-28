(*  Author:      David Sanan
    License:     LGPL
*)

(*  Title:      FactExample.thy
    Author:     David Sanan

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

(*<*)
theory FactExample 
imports HeapList VcgSeq
  "HOL-Statespace.StateSpaceSyntax" "HOL-Library.LaTeXsugar"
begin 
(*>*)


primrec fac:: "nat \<Rightarrow> nat"
where
"fac 0 = 1" |
"fac (Suc n) = (Suc n) * fac n"

(*<*)
lemma fac_simp [simp]: "0 < i \<Longrightarrow>  fac i = i * fac (i - 1)"
  by (cases i) simp_all
(*>*)

record vars =
  I_' :: nat
  M_' :: nat
 
definition Factorial 
  where "Factorial n \<equiv> 
  IF\<^sub>s (n = 0) THEN \<acute>I :==\<^sub>s 1
  ELSE 
    \<acute>I:==\<^sub>s 1;;\<^sub>s \<acute>M:==\<^sub>s 1;;\<^sub>s
    WHILE\<^sub>s (\<acute>M<n) INV \<lbrace>\<acute>M \<le> n \<and> \<acute>I = fac \<acute>M\<rbrace> DO\<^sub>s
      \<acute>M:==\<^sub>s \<acute>M + 1;;\<^sub>s
      \<acute>I:==\<^sub>s \<acute>I*\<acute>M
    OD
  FI
"

lemma "\<forall>n. \<Gamma>\<turnstile> \<lbrace>True\<rbrace> Factorial n \<lbrace>\<acute>I = fac n\<rbrace>"
  unfolding Factorial_def apply vcg 
  by auto


end
(*>*)
