(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      VCGCon.thy
    Author:     David Sanan, NTU

Copyright (C) 2015-2016 David Sanan 
Some rights reserved, NTU
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

section {* Facilitating the Hoare Logic *}
theory VcgCon 
imports  "EmbSimpl.VcgCommon" LocalRG_HoareDef 
keywords "procedures" "hoarestate" :: thy_decl
begin

locale hoare =
  fixes \<Gamma>::"('s,'p,'f,'e) body"

axiomatization NoBody::"('s,'p,'f,'e) com"
(* David added begin *)
ML_file "hoare.ML" 


(*method_setup hoare = "Hoare.hoare"
  "raw verification condition generator for Hoare Logic"

method_setup hoare_raw = "Hoare.hoare_raw"
  "even more raw verification condition generator for Hoare Logic"

method_setup vcg = "Hoare.vcg" 
  "verification condition generator for Hoare Logic"

method_setup vcg_step = "Hoare.vcg_step" 
  "single verification condition generation step with light simplification"


method_setup hoare_rule = "Hoare.hoare_rule" 
  "apply single hoare rule and solve certain sideconditions"
*)
text {* Variables of the programming language are represented as components 
of a record. To avoid cluttering up the namespace of Isabelle with lots of 
typical variable names, we append a unusual suffix at the end of each name by 
parsing
*}


definition to_normal::"'a \<Rightarrow> 'a \<Rightarrow>  ('a, 'b) xstate \<times> ('a, 'b) xstate"
where
"to_normal a b \<equiv> (Normal a,Normal b)"



subsection {* Some Fancy Syntax *}


(* priority guidline:
 * If command should be atomic for the guard it must have at least priority 21.
 *)

text {* reverse application *}
definition rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr "|>" 60)
  where "rapp x f = f x"


notation
  Skip  ("SKIP") and
  Throw  ("THROW")

syntax
  "_raise":: "'c \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f,'e) com"       ("(RAISE _ :==/ _)" [30, 30] 23)
  "_raise_ev":: "'c \<Rightarrow> 'e \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f,'e) com"       ("(RAISE _ :==(\<^sub>_)/ _)" [30, 30, 30] 23)
  "_seq"::"('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com" ("_;;/ _" [20, 21] 20)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("_\<surd>" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("_#" [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       ("_" [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         ("_" 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" ("_,/ _" [999,1000] 1000)
  "_guards"        :: "grds \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com" 
                                            ("(_/\<longmapsto> _)" [60, 21] 23)                                                           
  (* "_quote"       :: "'b => ('a => 'b)" *)
  "_Normal"       :: "'a => 'b"
  (* "_antiquoteCur0"  :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_antiquoteCur"  :: "('a => 'b) => 'b"
  "_antiquoteOld0"  :: "('a => 'b) => 'a => 'b"       ("\<^bsup>_\<^esup>_" [1000,1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b"
  "_Assert"      :: "'a => 'a set"           ("({|_|})" [0] 1000)  
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    ("({|_. _|})" [1000,0] 1000)
  "_AssertR"      :: "'a => 'a set"           ("({|_|}r)" [0] 1000)    *)
  "_Assign"      :: "'b => 'b => ('s,'p,'f,'e) com"    ("(_ :==/ _)" [30, 30] 23) 
  "_Assign_ev"      :: "'b => 'e \<Rightarrow>'b  \<Rightarrow> ('s,'p,'f,'e) com"    ("(_ :==(\<^sub>_)/ _)" [30,1000, 30] 23)
  "_Init"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f,'e) com" 
          ("(\<acute>_ :==\<^bsub>_\<^esub>/ _)" [30,1000, 30] 23)
   "_Init_ev"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'e \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f,'e) com" 
           ("(\<acute>_ :==(\<^sub>_)/ \<^bsub>_\<^esub>/ _)" [30,1000, 1000,30] 23) 
  "_GuardedAssign":: "'b => 'b => ('s,'p,'f,'e) com"    ("(_ :==\<^sub>g/ _)" [30, 30] 23)
  "_GuardedAssign_ev":: "'b => 'e \<Rightarrow> 'b => ('s,'p,'f,'e) com"    ("(_ :==\<^sub>g\<^sub>_/ _)" [30, 30, 30] 23)
  (* "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" ("(2\<acute>_ :==/ _)")
  ""             :: "newinit \<Rightarrow> newinits"    ("_")
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" ("_,/ _") *)
  "_New"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_New_ev"      :: "['a, 'e, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==(\<^sub>_)/(2 NEW _/ [_]))" [30, 30, 65, 0] 23)
  "_GuardedNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==\<^sub>g/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNew_ev"  :: "['a,'e, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==\<^sub>g\<^sub>_/(2 NEW _/ [_]))" [30, 30, 65, 0] 23)
  "_NNew"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==/(2 NNEW _/ [_]))" [30, 65, 0] 23)
  "_NNew_ev"         :: "['a, 'e, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==(\<^sub>_)/(2 NNEW _/ [_]))" [30, 30, 65, 0] 23)
  "_GuardedNNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==\<^sub>g/(2 NNEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNNew_ev"  :: "['a, 'e, 'b, newinits] \<Rightarrow> ('a,'b,'f,'e) com" 
                                            ("(_ :==\<^sub>g\<^sub>_/(2 NNEW _/ [_]))" [30, 30, 65, 0] 23)

  "_Cond"        :: "'a bexp => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com"
        ("(0IF (_)/ (2THEN/ _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com"
        ("(0IF (_)/ (2THEN/ _)/ FI)" [0, 0] 71)
  "_GuardedCond" :: "'a bexp => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com"
        ("(0IF\<^sub>g (_)/ (2THEN _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_GuardedCond_no_else":: "'a bexp => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com"
        ("(0IF\<^sub>g (_)/ (2THEN _)/ FI)" [0, 0] 71)
  "_Await" :: "'a bexp \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow>('s,'p,'f,'e) com"
        ("(0AWAIT (_)/ _)" [0, 0] 71)
  "_Await_ev" :: "'e \<Rightarrow> 'a bexp \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0AWAIT\<^sub>\<down>\<^sub>_ (_)/ _ )" [0,0, 0] 71)
  "_GuardedAwait" :: "'a bexp \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow>('s,'p,'f,'e) com"
        ("(0AWAIT\<^sub>g (_)/ _)" [0, 0] 71)
  "_GuardedAwait_ev" :: "'e \<Rightarrow> 'a bexp \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow>('s,'p,'f,'e) com"
        ("(0AWAIT\<^sub>g\<^sub>\<down>\<^sub>_ (_)/ _)" [0,0, 0] 71)
  "_While_inv_var"   :: "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_WhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_WhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_)/ FIX _./ INV (_) /_)"  [25, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_hook"   :: "'a bexp \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
  "_GuardedWhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/_)"  [25, 0, 0, 81] 71)

  "_GuardedWhile_inv_var":: 
       "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE\<^sub>g (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('s,'p,'f,'e) com"
        ("(0WHILE (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_GuardedWhile_inv"   :: "'a bexp => 'a assn => ('s,'p,'f,'e) com => ('s,'p,'f,'e) com"
        ("(0WHILE\<^sub>g (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_While"       :: "'a bexp => bdy => ('s,'p,'f,'e) com"
        ("(0WHILE (_) /_)"  [25, 81] 71)
  "_GuardedWhile"       :: "'a bexp => bdy => ('s,'p,'f,'e) com"
        ("(0WHILE\<^sub>g (_) /_)"  [25, 81] 71)
  "_While_guard"       :: "grds => 'a bexp => bdy => ('s,'p,'f,'e) com"
        ("(0WHILE (_/\<longmapsto> (1_)) /_)"  [1000,25,81] 71)
  "_While_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_/\<longmapsto> (1_)) INV (_) /_)"  [1000,25,0,81] 71)
  "_While_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>('a\<times>'a) set
                             \<Rightarrow>bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_/\<longmapsto> (1_)) INV (_)/ VAR (_) /_)"  [1000,25,0,0,81] 71)
  "_WhileFix_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)\<Rightarrow>('z\<Rightarrow>('a\<times>'a) set)
                             \<Rightarrow>bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/ VAR (_) /_)"  [1000,25,0,0,0,81] 71)
  "_WhileFix_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)
                             \<Rightarrow>bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/_)"  [1000,25,0,0,81] 71)

  "_Try_Catch":: "('s,'p,'f,'e) com \<Rightarrow>('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0TRY (_)/ (2CATCH _)/ END)"  [0,0] 71)

  "_DoPre" :: "('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com" 
  "_Do" :: "('s,'p,'f,'e) com \<Rightarrow> bdy" ("(2DO/ (_)) /OD" [0] 1000)
  "_Lab":: "'a bexp \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> bdy"
            ("_\<bullet>/_" [1000,71] 81)
  "":: "bdy \<Rightarrow> ('s,'p,'f,'e) com" ("_")
  "_Spec":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f,'e) com \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f,'e) com"
            ("(ANNO _. _/ (_)/ _,/_)" [0,1000,20,1000,1000] 60)
  "_SpecNoAbrupt":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f,'e) com \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f,'e) com"
            ("(ANNO _. _/ (_)/ _)" [0,1000,20,1000] 60)
  "_LemAnno":: "'n \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com"
              ("(0 LEMMA (_)/ _ END)" [1000,0] 71)
  (* "_locnoinit"    :: "ident \<Rightarrow> locinit"               ("\<acute>_")
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          ("(2\<acute>_ :==/ _)")
  ""             :: "locinit \<Rightarrow> locinits"             ("_")
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" ("_,/ _") *)
  "_Loc":: "[locinits,('s,'p,'f,'e) com] \<Rightarrow> ('s,'p,'f,'e) com"
                                         ("(2 LOC _;;/ (_) COL)" [0,0] 71) 
  "_Switch":: "('s \<Rightarrow> 'v) \<Rightarrow> switchcases \<Rightarrow> ('s,'p,'f,'e) com"
              ("(0 SWITCH (_)/ _ END)" [22,0] 71)
  "_switchcase":: "'v set \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> switchcase" ("_\<Rightarrow>/ _" )
  (* "_switchcasesSingle"  :: "switchcase \<Rightarrow> switchcases" ("_")         
  "_switchcasesCons":: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases"
                       ("_/ | _") *)
  "_Basic":: "basicblock \<Rightarrow> ('s,'p,'f,'e) com" ("(0BASIC/ (_)/ END)" [22] 71)
  "_Basic_ev":: "'e \<Rightarrow> basicblock \<Rightarrow> ('s,'p,'f,'e) com" ("(0BASIC(\<^sub>_)/ (_)/ END)" [22, 22] 71)
  (* "_BasicBlock":: "basics \<Rightarrow> basicblock" ("_")
  "_BAssign"   :: "'b => 'b => basic"    ("(_ :==/ _)" [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             ("_")
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" ("_,/ _") *)

(* Experimental coloring for ProofGeneral; fails to run through latex*)
(*<*)
(* syntax (ProofGeneral output)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("F_A" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("B_A" [1000] 1000) *)
(*>*)

syntax (ascii)
  "_While_guard"       :: "grds => 'a bexp => bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_|-> /_) /_)"  [0,0,1000] 71)
  "_While_guard_inv":: "grds\<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('s,'p,'f,'e) com"
        ("(0WHILE (_|-> /_) INV (_) /_)"  [0,0,0,1000] 71)
  "_guards" :: "grds \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com" ("(_|->_ )" [60, 21] 23)




syntax (output)
  "_hidden_grds"      :: "grds" ("\<dots>")

translations
  "_Do c" => "c"
  "b\<bullet> c" => "CONST condCatch c b SKIP"
  "b\<bullet> (_DoPre c)" <= "CONST condCatch c b SKIP"
  "l\<bullet> (CONST whileAnnoG gs b I V c)" <= "l\<bullet> (_DoPre (CONST whileAnnoG gs b I V c))"
  "l\<bullet> (CONST whileAnno b I V c)" <= "l\<bullet> (_DoPre (CONST whileAnno b I V c))"
  "CONST condCatch c b SKIP" <= "(_DoPre (CONST condCatch c b SKIP))"
  "_Do c" <= "_DoPre c"
  "c;; d" == "CONST Seq c d"
  "_guarantee g" => "(CONST True, g)"
  "_guaranteeStrip g" == "CONST guaranteeStripPair (CONST True) g"
  "_grd g" => "(CONST False, g)"
  "_grds g gs" => "g#gs"
  "_last_grd g" => "[g]"
  "_guards gs c" == "CONST guards gs c"  
   
  "IF b THEN c1 ELSE c2 FI" => "CONST Cond {|b|} c1 c2"
  "IF b THEN c1 FI"         ==  "IF b THEN c1 ELSE SKIP FI"
  "IF\<^sub>g b THEN c1 FI"        ==  "IF\<^sub>g b THEN c1 ELSE SKIP FI"

  "AWAIT b c" == "CONST Await {|b|} c (CONST None)"
  "AWAIT\<^sub>\<down>\<^sub>e b c " == "CONST Await {|b|} c (CONST Some e)"

  "_While_inv_var b I V c"          => "CONST whileAnno {|b|} I V c"
  "_While_inv_var b I V (_DoPre c)" <= "CONST whileAnno {|b|} I V c"
  "_While_inv b I c"                 == "_While_inv_var b I (CONST undefined) c"
  "_While b c"                       == "_While_inv b {|CONST undefined|} c"

  "_While_guard_inv_var gs b I V c"          => "CONST whileAnnoG gs {|b|} I V c"
(*  "_While_guard_inv_var gs b I V (_DoPre c)" <= "CONST whileAnnoG gs {|b|} I V c"*)
  "_While_guard_inv gs b I c"       == "_While_guard_inv_var gs b I (CONST undefined) c"
  "_While_guard gs b c"             == "_While_guard_inv gs b {|CONST undefined|} c"

  "_GuardedWhile_inv b I c"  == "_GuardedWhile_inv_var b I (CONST undefined) c"
  "_GuardedWhile b c"        == "_GuardedWhile_inv b {|CONST undefined|} c"
(*  "\<^bsup>s\<^esup>A"                      => "A s"*)
  "TRY c1 CATCH c2 END"     == "CONST Catch c1 c2"
  "ANNO s. P c Q,A" => "CONST specAnno (\<lambda>s. P) (\<lambda>s. c) (\<lambda>s. Q) (\<lambda>s. A)"
  "ANNO s. P c Q" == "ANNO s. P c Q,{}"

  "_WhileFix_inv_var b z I V c" => "CONST whileAnnoFix {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_inv_var b z I V (_DoPre c)" <= "_WhileFix_inv_var {|b|} z I V c"
  "_WhileFix_inv b z I c" == "_WhileFix_inv_var b z I (CONST undefined) c"

  "_GuardedWhileFix_inv b z I c" == "_GuardedWhileFix_inv_var b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_var b z I V c" =>
                         "_GuardedWhileFix_inv_var_hook {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"

  "_WhileFix_guard_inv_var gs b z I V c" => 
                                      "CONST whileAnnoGFix gs {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_guard_inv_var gs b z I V (_DoPre c)" <= 
                                      "_WhileFix_guard_inv_var gs {|b|} z I V c"
  "_WhileFix_guard_inv gs b z I c" == "_WhileFix_guard_inv_var gs b z I (CONST undefined) c"
  "LEMMA x c END" == "CONST lem x c"
translations
 "(_switchcase V c)" => "(V,c)"
 (* "(_switchcasesSingle b)" => "[b]"
 "(_switchcasesCons b bs)" => "CONST Cons b bs" *)
 "(_Switch v vs)" => "CONST switch (_quote v) vs"



print_ast_translation {*
  let
    fun dest_abs (Ast.Appl [Ast.Constant @{syntax_const "_abs"}, x, t]) = (x, t)
      | dest_abs _ = raise Match;
    fun spec_tr' [P, c, Q, A] =
      let 
        val (x',P') = dest_abs P;
        val (_ ,c') = dest_abs c;
        val (_ ,Q') = dest_abs Q;
        val (_ ,A') = dest_abs A; 
      in
        if (A' = Ast.Constant @{const_syntax bot})
        then Ast.mk_appl (Ast.Constant @{syntax_const "_SpecNoAbrupt"}) [x', P', c', Q'] 
        else Ast.mk_appl (Ast.Constant @{syntax_const "_Spec"}) [x', P', c', Q', A']
      end;
    fun whileAnnoFix_tr' [b, I, V, c] =
      let
        val (x',I') = dest_abs I;
        val (_ ,V') = dest_abs V;
        val (_ ,c') = dest_abs c;
      in
        Ast.mk_appl (Ast.Constant @{syntax_const "_WhileFix_inv_var"}) [b, x', I', V', c']
      end;
  in
   [(@{const_syntax specAnno}, K spec_tr'),
    (@{const_syntax whileAnnoFix}, K whileAnnoFix_tr')]
  end
*}



(* nonterminal par and pars and actuals

syntax 
  "_par" :: "'a \<Rightarrow> par"                                ("_")
  ""    :: "par \<Rightarrow> pars"                               ("_")
  "_pars" :: "[par,pars] \<Rightarrow> pars"                      ("_,/_")
  "_actuals" :: "pars \<Rightarrow> actuals"                      ("'(_')")
  "_actuals_empty" :: "actuals"                        ("'(')") *)

syntax "_Call" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" ("CALL __" [1000,1000] 21)
       "_GuardedCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" ("CALL\<^sub>g __" [1000,1000] 21)
       "_CallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== CALL __" [30,1000,1000] 21)
       "_Proc" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" ("PROC __" 21)
       "_ProcAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== PROC __" [30,1000,1000] 21)
       "_GuardedCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== CALL\<^sub>g __" [30,1000,1000] 21)
       "_DynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" ("DYNCALL __" [1000,1000] 21)
       "_GuardedDynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" ("DYNCALL\<^sub>g __" [1000,1000] 21)
       "_DynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== DYNCALL __" [30,1000,1000] 21)
       "_GuardedDynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== DYNCALL\<^sub>g __" [30,1000,1000] 21)
             
       "_Call_ev" :: "'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
          ("CALL\<^sub>E _____" [1000,1000,1000,1000,1000] 21)
       "_GuardedCall_ev" :: "'p \<Rightarrow> actuals \<Rightarrow>  'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
          ("CALL\<^sub>E\<^sub>g _____" [1000,1000,1000,1000,1000] 21)
       "_CallAss_ev":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== CALL\<^sub>E _____" [30,1000,1000,1000,1000,1000] 21)
       "_Proc_ev" :: "'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
             ("PROC\<^sub>E _____" 21)
       "_ProcAss_ev":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== PROC\<^sub>E _____" [30,1000,1000,1000,1000,1000] 21)
       "_GuardedCallAss_ev":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow>(('a,string,'f,'e) com)" 
             ("_ :== CALL\<^sub>E\<^sub>g _____" [30,1000,1000,1000,1000,1000] 21)
       "_DynCall_ev" :: "'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow>(('a,string,'f,'e) com)" 
             ("DYNCALL\<^sub>E _____" [1000,1000,1000,1000,1000] 21)
       "_GuardedDynCall_ev" :: "'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
           ("DYNCALL\<^sub>e\<^sub>g _____" [1000,1000,1000,1000,1000] 21)
       "_DynCallAss_ev":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow>'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> (('a,string,'f,'e) com)" 
             ("_ :== DYNCALL _____" [30,1000,1000,1000,1000,1000] 21)
       "_GuardedDynCallAss_ev":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow> 'e option \<Rightarrow>(('a,string,'f,'e) com)" 
             ("_ :== DYNCALL\<^sub>g _____" [30,1000,1000,1000,1000,1000] 21)
             
       

       "_Bind":: "['s \<Rightarrow> 'v, idt, 'v \<Rightarrow> ('s,'p,'f,'e) com] \<Rightarrow> ('s,'p,'f,'e) com" 
                      ("_ \<ggreater> _./ _" [22,1000,21] 21)
       "_bseq"::"('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) com" 
           ("_\<ggreater>/ _" [22, 21] 21)
           
       "_FCall" :: "['p,actuals,idt,(('a,string,'f,'e) com)]\<Rightarrow> (('a,string,'f,'e) com)" 
                      ("CALL __ \<ggreater> _./ _" [1000,1000,1000,21] 21)
       "_FCall_ev" :: "['p,actuals,'e option,'e option,'e option,idt,(('a,string,'f,'e) com)]\<Rightarrow> (('a,string,'f,'e) com)" 
                      ("CALL\<^sub>e __ ___\<ggreater> _./ _" [1000,1000,1000,1000,1000,1000,21] 21)



translations
"_Bind e i c" == "CONST bind (_quote e) (\<lambda>i. c)"
"_FCall p acts i c" == "_FCall p acts (\<lambda>i. c)"
"_bseq c d" == "CONST bseq c d"



definition Let':: "['a, 'a => 'b] => 'b"
  where "Let' = Let"

  
ML_file "hoare_syntax.ML"




(* decorate state components with suffix *)
(*
parse_ast_translation {*
 [(@{syntax_const "_Free"}, K Hoare_Syntax.free_arg_ast_tr),
  (@{syntax_const "_In"}, K Hoare_Syntax.in_arg_ast_tr),
  (@{syntax_const "_Where"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_Where"}),
  (@{syntax_const "_WhereElse"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_WhereElse"})
] 
*}
*)
(*
parse_ast_translation {*
 [(@{syntax_const "_antiquoteOld"},
    Hoare_Syntax.antiquoteOld_varname_tr @{syntax_const "_antiquoteOld"})]
*}
*)




parse_translation {*
  let val ev1 = (Syntax.const @{const_syntax None}); 
       val ev2 = (Syntax.const @{const_syntax None});
       val ev3 = (Syntax.const @{const_syntax None}) in
  [(@{syntax_const "_Call"}, Hoare_Syntax.call_tr false false ev1 ev2 ev3),
  (@{syntax_const "_FCall"}, Hoare_Syntax.fcall_tr ev1 ev2 ev3),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_tr false false ev1 ev2 ev3),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.call_tr false true ev1 ev2 ev3),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.call_ass_tr false true ev1 ev2 ev3),
  (@{syntax_const "_Proc"}, Hoare_Syntax.proc_tr ev1 ev2 ev3),
  (@{syntax_const "_ProcAss"}, Hoare_Syntax.proc_ass_tr ev1 ev2 ev3),
  (@{syntax_const "_DynCall"}, Hoare_Syntax.call_tr true false ev1 ev2 ev3),
  (@{syntax_const "_DynCallAss"}, Hoare_Syntax.call_ass_tr true false ev1 ev2 ev3),
  (@{syntax_const "_GuardedDynCall"}, Hoare_Syntax.call_tr true true ev1 ev2 ev3),
  (@{syntax_const "_GuardedDynCallAss"}, Hoare_Syntax.call_ass_tr true true ev1 ev2 ev3),
  (@{syntax_const "_Call_ev"}, Hoare_Syntax.call_ev_tr false false),
  (@{syntax_const "_FCall_ev"}, Hoare_Syntax.fcall_ev_tr),
  (@{syntax_const "_CallAss_ev"}, Hoare_Syntax.call_ass_ev_tr false false),
  (@{syntax_const "_GuardedCall_ev"}, Hoare_Syntax.call_ev_tr false true),
  (@{syntax_const "_GuardedCallAss_ev"}, Hoare_Syntax.call_ass_ev_tr false true),
  (@{syntax_const "_Proc_ev"}, Hoare_Syntax.proc_ev_tr),
  (@{syntax_const "_ProcAss_ev"}, Hoare_Syntax.proc_ass_ev_tr),
  (@{syntax_const "_DynCall_ev"}, Hoare_Syntax.call_ev_tr true false),
  (@{syntax_const "_DynCallAss_ev"}, Hoare_Syntax.call_ass_ev_tr true false),
  (@{syntax_const "_GuardedDynCall_ev"}, Hoare_Syntax.call_ev_tr true true),
  (@{syntax_const "_GuardedDynCallAss_ev"}, Hoare_Syntax.call_ass_ev_tr true true)]
 end
*}

(*
  (@{syntax_const "_Call"}, Hoare_Syntax.call_ast_tr),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_ast_tr),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.guarded_call_ast_tr),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.guarded_call_ass_ast_tr)
*)


parse_translation {*
 [(@{syntax_const "_Assign"}, Hoare_Syntax.assign_tr),
  (@{syntax_const "_Assign_ev"}, Hoare_Syntax.assign_ev_tr),
  (@{syntax_const "_raise"}, Hoare_Syntax.raise_tr),
  (@{syntax_const "_raise_ev"}, Hoare_Syntax.raise_ev_tr),
  (@{syntax_const "_New"}, Hoare_Syntax.new_tr),
  (@{syntax_const "_New_ev"}, Hoare_Syntax.new_ev_tr),
  (@{syntax_const "_NNew"}, Hoare_Syntax.nnew_tr),
  (@{syntax_const "_NNew_ev"}, Hoare_Syntax.nnew_ev_tr),
  (@{syntax_const "_GuardedAssign"}, Hoare_Syntax.guarded_Assign_tr),
  (@{syntax_const "_GuardedAssign_ev"}, Hoare_Syntax.guarded_Assign_ev_tr),
  (@{syntax_const "_GuardedNew"}, Hoare_Syntax.guarded_New_tr),
  (@{syntax_const "_GuardedNNew"}, Hoare_Syntax.guarded_NNew_tr),
  (@{syntax_const "_GuardedNew_ev"}, Hoare_Syntax.guarded_New_ev_tr),
  (@{syntax_const "_GuardedNNew_ev"}, Hoare_Syntax.guarded_NNew_ev_tr),
  (@{syntax_const "_GuardedWhile_inv_var"}, Hoare_Syntax.guarded_While_tr),
  (@{syntax_const "_GuardedWhileFix_inv_var_hook"}, Hoare_Syntax.guarded_WhileFix_tr),
  (@{syntax_const "_GuardedCond"}, Hoare_Syntax.guarded_Cond_tr), 
  (@{syntax_const "_GuardedAwait"}, Hoare_Syntax.guarded_Await_tr),
  (@{syntax_const "_GuardedAwait_ev"}, Hoare_Syntax.guarded_Await_ev_tr),
  (@{syntax_const "_Basic"}, Hoare_Syntax.basic_tr),
  (@{syntax_const "_Basic_ev"}, Hoare_Syntax.basic_ev_tr)]
*}

parse_translation {*
 [(@{syntax_const "_Init"}, Hoare_Syntax.init_tr),
  (* (@{syntax_const "_Init_ev"}, Hoare_Syntax.init_ev_tr), *)
  (@{syntax_const "_Loc"}, Hoare_Syntax.loc_tr)] 
*}


print_translation {*
 [(@{const_syntax Basic}, Hoare_Syntax.assign_tr'),
  (@{const_syntax raise}, Hoare_Syntax.raise_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.new_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.init_tr'),
  (@{const_syntax Spec}, Hoare_Syntax.nnew_tr'),
  (@{const_syntax block}, Hoare_Syntax.loc_tr'),
  (@{const_syntax Collect}, Hoare_Syntax.assert_tr'),
  (@{const_syntax Cond}, Hoare_Syntax.bexp_tr' "_Cond"),
  (@{const_syntax switch}, Hoare_Syntax.switch_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.basic_tr'),
  (@{const_syntax guards}, Hoare_Syntax.guards_tr'),
  (@{const_syntax whileAnnoG}, Hoare_Syntax.whileAnnoG_tr'),
  (@{const_syntax whileAnnoGFix}, Hoare_Syntax.whileAnnoGFix_tr'),
  (@{const_syntax bind}, Hoare_Syntax.bind_tr')]
*}


print_translation {*
  let
    fun spec_tr' ctxt ((coll as Const _)$
                   ((splt as Const _) $ (t as (Abs (s,T,p))))::ts) =
          let
            fun selector (Const (c, T)) = Hoare.is_state_var c
              | selector (Const (@{syntax_const "_free"}, _) $ (Free (c, T))) =
                  Hoare.is_state_var c
              | selector _ = false;
          in
            if Hoare_Syntax.antiquote_applied_only_to selector p then
              Syntax.const @{const_syntax Spec} $ coll $
                (splt $ Hoare_Syntax.quote_mult_tr' ctxt selector
                    Hoare_Syntax.antiquoteCur Hoare_Syntax.antiquoteOld  (Abs (s,T,t)))
             else raise Match
          end
      | spec_tr' _ ts = raise Match
  in [(@{const_syntax Spec}, spec_tr')] end
*}


print_translation {*
 [(@{const_syntax call}, Hoare_Syntax.call_tr'),
  (@{const_syntax dynCall}, Hoare_Syntax.dyn_call_tr'),
  (@{const_syntax fcall}, Hoare_Syntax.fcall_tr'),
  (@{const_syntax Call}, Hoare_Syntax.proc_tr')]
*}

(*Syntax for the Parallel operator *)
nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR ps" \<rightharpoonup> "ps"

syntax
  "_prg_scheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"  ("SCHEME [_ \<le> _ < _] _" [0,0,0,60] 57)

translations
  "_prg_scheme j i k c" \<rightleftharpoons> "(CONST map (\<lambda>i. c) [j..<k])"

text \<open>Translations for variables before and after a transition:\<close>

syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" == "x \<acute> CONST fst"
  "\<ordfeminine>x" == "x \<acute> CONST snd"

(* print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquoteOld0"} t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax Basic}, K assign_tr'),
    (@{const_syntax Cond}, K (bexp_tr' @{syntax_const "_Cond"})),
    (@{const_syntax While}, K (bexp_tr' @{syntax_const "_While"}))]
  end 
\<close> *)
end