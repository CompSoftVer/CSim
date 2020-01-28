(*  Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Vcg.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

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
theory VcgSeq
imports "../common/VcgCommon"
keywords "procedures_s" "hoarestate_s" :: thy_decl
begin

axiomatization NoBody::"('s,'p,'f) Language.com"

ML_file "hoare.ML"

method_setup hoare = "Hoare.hoare"
  "raw verification condition generator for Hoare Logic"

method_setup hoare_raw = "Hoare.hoare_raw"
  "even more raw verification condition generator for Hoare Logic"

method_setup vcg = "Hoare.vcg" 
  "verification condition generator for Hoare Logic"

method_setup vcg_step = "Hoare.vcg_step" 
  "single verification condition generation step with light simplification"


method_setup hoare_rule = "Hoare.hoare_rule" 
  "apply single hoare rule and solve certain sideconditions"

text {* Variables of the programming language are represented as components 
of a record. To avoid cluttering up the namespace of Isabelle with lots of 
typical variable names, we append a unusual suffix at the end of each name by 
parsing
*}

(* definition list_multsel:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" (infixl "!!" 100)
  where "xs !! ns = map (nth xs) ns"

definition list_multupd:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "list_multupd xs ns ys = foldl (\<lambda>xs (n,v). xs[n:=v]) xs (zip ns ys)" 

nonterminal lmupdbinds and lmupdbind 

syntax
  -- {* multiple list update *}
  "_lmupdbind":: "['a, 'a] => lmupdbind"    ("(2_ [:=]/ _)")
  "" :: "lmupdbind => lmupdbinds"    ("_")
  "_lmupdbinds" :: "[lmupdbind, lmupdbinds] => lmupdbinds"    ("_,/ _")
  "_LMUpdate" :: "['a, lmupdbinds] => 'a"    ("_/[(_)]" [900,0] 900) 

translations
  "_LMUpdate xs (_lmupdbinds b bs)" == "_LMUpdate (_LMUpdate xs b) bs"
  "xs[is[:=]ys]" == "CONST list_multupd xs is ys" *)


subsection {* Some Fancy Syntax *}


(* priority guidline:
 * If command should be atomic for the guard it must have at least priority 21.
 *)

(* text {* reverse application *}
definition rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr "|>" 60)
  where "rapp x f = f x" *)


    
  
  

notation
  Skip  ("SKIP\<^sub>s") and
  Throw  ("THROW\<^sub>s")

syntax
  "_raise_s":: "'c \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f) Language.com"       ("(RAISE\<^sub>s _ :==\<^sub>s/ _)" [30, 30] 23)
  "_seq_s"::"('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" ("_;;\<^sub>s/ _" [20, 21] 20)
  (* "_guarantee"     :: "'s set \<Rightarrow> grd"       ("_\<surd>" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("_#" [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       ("_" [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         ("_" 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" ("_,/ _" [999,1000] 1000) *)
  "_guards_s"        :: "grds \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" 
                                            ("(_/\<longmapsto>\<^sub>s _)" [60, 21] 23)                                                           
  (*"_quote"       :: "'b => ('a => 'b)"
  "_antiquoteCur0"  :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_antiquoteCur"  :: "('a => 'b) => 'b"
  "_antiquoteOld0"  :: "('a => 'b) => 'a => 'b"       ("\<^bsup>_\<^esup>_" [1000,1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b" 
  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     ("(\<lbrace>_. _\<rbrace>)" [1000,0] 1000) *)
  "_Assign_s"      :: "'b => 'b => ('a,'p,'f) Language.com"    ("(_ :==\<^sub>s/ _)" [30, 30] 23)
  "_Init_s"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> ('a,'p,'f) Language.com" 
                                             ("(\<acute>_ :==\<^sub>s\<^bsub>_\<^esub>/ _)" [30,1000, 30] 23)
  "_GuardedAssign_s":: "'b => 'b => ('a,'p,'f) Language.com"    ("(_ :==\<^sub>s\<^sub>g/ _)" [30, 30] 23)
  (* "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" ("(2\<acute>_ :==/ _)")
  ""             :: "newinit \<Rightarrow> newinits"    ("_")
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" ("_,/ _") *)
  "_New_s"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com" 
                                            ("(_ :==\<^sub>s/(2 NEW\<^sub>s _/ [_]))" [30, 65, 0] 23)
  "_GuardedNew_s"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com" 
                                            ("(_ :==\<^sub>s\<^sub>g/(2 NEW\<^sub>e _/ [_]))" [30, 65, 0] 23)
  "_NNew_s"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com" 
                                            ("(_ :==\<^sub>s/(2 NNEW\<^sub>s _/ [_]))" [30, 65, 0] 23)
  "_GuardedNNew_s"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) Language.com" 
                                            ("(_ :==\<^sub>s\<^sub>g/(2 NNEW\<^sub>s _/ [_]))" [30, 65, 0] 23)

  "_Cond_s"        :: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s (_)/ (2THEN/ _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_Cond_no_else_s":: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s (_)/ (2THEN/ _)/ FI)" [0, 0] 71)
  "_GuardedCond_s" :: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s\<^sub>g (_)/ (2THEN _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_GuardedCond_no_else_s":: "'a bexp => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0IF\<^sub>s\<^sub>g (_)/ (2THEN _)/ FI)" [0, 0] 71)
  "_While_inv_var_s"   :: "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_WhileFix_inv_var_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_WhileFix_inv_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ FIX _./ INV (_) /_)"  [25, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s\<^sub>g (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_hook_s"   :: "'a bexp \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
  "_GuardedWhileFix_inv_s"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s\<^sub>g (_)/ FIX _./ INV (_)/_)"  [25, 0, 0, 81] 71)

  "_GuardedWhile_inv_var_s":: 
       "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s\<^sub>g (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_While_inv_s"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_GuardedWhile_inv_s"   :: "'a bexp => 'a assn => ('a,'p,'f) Language.com => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s\<^sub>g (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_While_s"       :: "'a bexp => bdy => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_) /_)"  [25, 81] 71)
  "_GuardedWhile_s"       :: "'a bexp => bdy => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s\<^sub>g (_) /_)"  [25, 81] 71)
  "_While_guard_s"       :: "grds => 'a bexp => bdy => ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) /_)"  [1000,25,81] 71)
  "_While_guard_inv_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) INV (_) /_)"  [1000,25,0,81] 71)
  "_While_guard_inv_var_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>('a\<times>'a) set
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) INV (_)/ VAR (_) /_)"  [1000,25,0,0,81] 71)
  "_WhileFix_guard_inv_var_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)\<Rightarrow>('z\<Rightarrow>('a\<times>'a) set)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) FIX _./ INV (_)/ VAR (_) /_)"  [1000,25,0,0,0,81] 71)
  "_WhileFix_guard_inv_s":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_/\<longmapsto> (1_)) FIX _./ INV (_)/_)"  [1000,25,0,0,81] 71)

  "_Try_Catch_s":: "('a,'p,'f) Language.com \<Rightarrow>('a,'p,'f) Language.com \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0TRY\<^sub>s (_)/ (2CATCH _)/ END)"  [0,0] 71)

  "_DoPre_s" :: "('a,'p,'f) Language.com \<Rightarrow> ('a,'p,'f) Language.com" 
  "_Do_s" :: "('a,'p,'f) Language.com \<Rightarrow> bdy" ("(2DO\<^sub>s/ (_)) /OD" [0] 1000)
  "_Lab_s":: "'a bexp \<Rightarrow> ('a,'p,'f) Language.com \<Rightarrow> bdy"
            ("_\<bullet>\<^sub>s /_" [1000,71] 81)
  "":: "bdy \<Rightarrow> ('a,'p,'f) Language.com" ("_")
  "_Spec_s":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) Language.com \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) Language.com"
            ("(ANNO\<^sub>s _. _/ (_)/ _,/_)" [0,1000,20,1000,1000] 60)
  "_SpecNoAbrupt_s":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) Language.com \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) Language.com"
            ("(ANNO\<^sub>s _. _/ (_)/ _)" [0,1000,20,1000] 60)
  "_LemAnno_s":: "'n \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com"
              ("(0 LEMMA\<^sub>s (_)/ _ END)" [1000,0] 71)
  (* "_locnoinit"    :: "ident \<Rightarrow> locinit"               ("\<acute>_")
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          ("(2\<acute>_ :==/ _)")
  ""             :: "locinit \<Rightarrow> locinits"             ("_") 
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" ("_,/ _") *)
  "_Loc_s":: "[locinits,('s,'p,'f) Language.com] \<Rightarrow> ('s,'p,'f) Language.com"
                                         ("(2 LOC\<^sub>s _;;/ (_) COL)" [0,0] 71)
  "_Switch_s":: "('s \<Rightarrow> 'v) \<Rightarrow> switchcases \<Rightarrow> ('s,'p,'f) Language.com"
              ("(0 SWITCH\<^sub>s (_)/ _ END)" [22,0] 71)
  "_switchcase_s":: "'v set \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> switchcase" ("_\<Rightarrow>\<^sub>s/ _" )
  (* "_switchcasesSingle"  :: "switchcase \<Rightarrow> switchcases" ("_")         
  "_switchcasesCons":: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases"
                       ("_/ | _") *)
  "_Basic_s":: "basicblock \<Rightarrow> ('s,'p,'f) Language.com" ("(0BASIC\<^sub>s/ (_)/ END)" [22] 71)
  (* "_BasicBlock":: "basics \<Rightarrow> basicblock" ("_")
  "_BAssign"   :: "'b => 'b => basic"    ("(_ :==/ _)" [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             ("_")
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" ("_,/ _") *)

syntax (ASCII)
  (*"_Assert"      :: "'a => 'a set"           ("({|_|})" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    ("({|_. _|})" [1000,0] 1000) *)
  "_While_guard_s"       :: "grds => 'a bexp => bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_|-> /_) /_)"  [0,0,1000] 71)
  "_While_guard_inv_s":: "grds\<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) Language.com"
        ("(0WHILE\<^sub>s (_|-> /_) INV (_) /_)"  [0,0,0,1000] 71)
  "_guards_s" :: "grds \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" ("(_|->_ )" [60, 21] 23)

syntax (output)
  "_hidden_grds"      :: "grds" ("\<dots>")

translations
  "_Do_s c" => "c"
  "b\<bullet>\<^sub>s c" => "CONST condCatch c b SKIP\<^sub>s"
  "b\<bullet>\<^sub>s (_DoPre_s c)" <= "CONST condCatch c b SKIP\<^sub>s"
  "l\<bullet>\<^sub>s (CONST whileAnnoG gs b I V c)" <= "l\<bullet>\<^sub>s (_DoPre_s (CONST whileAnnoG gs b I V c))"
  "l\<bullet>\<^sub>s (CONST whileAnno b I V c)" <= "l\<bullet>\<^sub>s (_DoPre_s (CONST whileAnno b I V c))"
  "CONST condCatch c b SKIP\<^sub>s" <= "(_DoPre_s (CONST condCatch c b SKIP\<^sub>s))"
  "_Do_s c" <= "_DoPre_s c"
  "c;;\<^sub>s d" == "CONST Seq c d"
  "_guarantee g" => "(CONST True, g)"
  "_guaranteeStrip g" == "CONST guaranteeStripPair (CONST True) g"
  "_grd g" => "(CONST False, g)"
  "_grds g gs" => "g#gs"
  "_last_grd g" => "[g]"
  "_guards_s gs c" == "CONST guards gs c" 
  "IF\<^sub>s b THEN c1 ELSE c2 FI" => "CONST Cond {|b|} c1 c2"
  "IF\<^sub>s b THEN c1 FI"         ==  "IF\<^sub>s b THEN c1 ELSE SKIP\<^sub>s FI"
  "IF\<^sub>s\<^sub>g b THEN c1 FI"        ==  "IF\<^sub>s\<^sub>g b THEN c1 ELSE SKIP\<^sub>s FI"

  "_While_inv_var_s b I V c"          => "CONST whileAnno {|b|} I V c"
  "_While_inv_var_s b I V (_DoPre_s c)" <= "CONST whileAnno {|b|} I V c"
  "_While_inv_s b I c"                 == "_While_inv_var_s b I (CONST undefined) c"
  "_While_s b c"                       == "_While_inv_s b {|CONST undefined|} c"

  "_While_guard_inv_var_s gs b I V c"          => "CONST whileAnnoG gs {|b|} I V c"
(*  "_While_guard_inv_var gs b I V (_DoPre c)" <= "CONST whileAnnoG gs {|b|} I V c"*)
  "_While_guard_inv_s gs b I c"       == "_While_guard_inv_var_s gs b I (CONST undefined) c"
  "_While_guard_s gs b c"             == "_While_guard_inv_s gs b {|CONST undefined|} c"

  "_GuardedWhile_inv_s b I c"  == "_GuardedWhile_inv_var_s b I (CONST undefined) c"
  "_GuardedWhile_s b c"        == "_GuardedWhile_inv_s b {|CONST undefined|} c"
(*  "\<^bsup>s\<^esup>A"                      => "A s"*)
  "TRY\<^sub>s c1 CATCH c2 END"     == "CONST Catch c1 c2"
  "ANNO\<^sub>s s. P c Q,A" => "CONST specAnno (\<lambda>s. P) (\<lambda>s. c) (\<lambda>s. Q) (\<lambda>s. A)"
  "ANNO\<^sub>s s. P c Q" == "ANNO\<^sub>s s. P c Q,{}"

  "_WhileFix_inv_var_s b z I V c" => "CONST whileAnnoFix {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_inv_var_s b z I V (_DoPre_s c)" <= "_WhileFix_inv_var_s {|b|} z I V c"
  "_WhileFix_inv_s b z I c" == "_WhileFix_inv_var_s b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_s b z I c" == "_GuardedWhileFix_inv_var_s b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_var_s b z I V c" =>
                         "_GuardedWhileFix_inv_var_hook_s {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"

  "_WhileFix_guard_inv_var_s gs b z I V c" => 
                                      "CONST whileAnnoGFix gs {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_guard_inv_var_s gs b z I V (_DoPre_s c)" <= 
                                      "_WhileFix_guard_inv_var_s gs {|b|} z I V c"
  "_WhileFix_guard_inv_s gs b z I c" == "_WhileFix_guard_inv_var_s gs b z I (CONST undefined) c"
  "LEMMA\<^sub>s x c END" == "CONST lem x c"
translations
 "(_switchcase_s V c)" => "(V,c)"
(* "(_switchcasesSingle b)" => "[b]"
 "(_switchcasesCons b bs)" => "CONST Cons b bs" *)
 "(_Switch_s v vs)" => "CONST switch (_quote v) vs"

(*parse_ast_translation {*
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) (map Ast.strip_positions asts)
  in
   [(@{syntax_const "_antiquoteCur0"}, K (tr @{syntax_const "_antiquoteCur"})),
    (@{syntax_const "_antiquoteOld0"}, K (tr @{syntax_const "_antiquoteOld"}))]
  end
*} *)

(* print_ast_translation {*
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) asts
  in
   [(@{syntax_const "_antiquoteCur"}, K (tr @{syntax_const "_antiquoteCur0"})),
    (@{syntax_const "_antiquoteOld"}, K (tr @{syntax_const "_antiquoteOld0"}))]
  end
*} *)

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
        then Ast.mk_appl (Ast.Constant @{syntax_const "_SpecNoAbrupt_s"}) [x', P', c', Q'] 
        else Ast.mk_appl (Ast.Constant @{syntax_const "_Spec_s"}) [x', P', c', Q', A']
      end;
    fun whileAnnoFix_tr' [b, I, V, c] =
      let
        val (x',I') = dest_abs I;
        val (_ ,V') = dest_abs V;
        val (_ ,c') = dest_abs c;
      in
        Ast.mk_appl (Ast.Constant @{syntax_const "_WhileFix_inv_var_s"}) [b, x', I', V', c']
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

syntax "_Call_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("CALL\<^sub>s __" [1000,1000] 21)
       "_GuardedCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("CALL\<^sub>s\<^sub>g __" [1000,1000] 21)
       "_CallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" 
             ("_ :== CALL\<^sub>s __" [30,1000,1000] 21)
       "_Proc_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("PROC\<^sub>s __" 21)
       "_ProcAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" 
             ("_ :== PROC\<^sub>s __" [30,1000,1000] 21)
       "_GuardedCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" 
             ("_ :== CALL\<^sub>s\<^sub>g __" [30,1000,1000] 21)
       "_DynCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("DYNCALL\<^sub>s __" [1000,1000] 21)
       "_GuardedDynCall_s" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" ("DYNCALL\<^sub>s\<^sub>g __" [1000,1000] 21)
       "_DynCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" 
             ("_ :== DYNCALL\<^sub>s __" [30,1000,1000] 21)
       "_GuardedDynCallAss_s":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) Language.com)" 
             ("_ :== DYNCALL\<^sub>s\<^sub>g __" [30,1000,1000] 21)

       "_Bind_s":: "['s \<Rightarrow> 'v, idt, 'v \<Rightarrow> ('s,'p,'f) Language.com] \<Rightarrow> ('s,'p,'f) Language.com" 
                      ("_ \<ggreater>\<^sub>s _./ _" [22,1000,21] 21)
       "_bseq_s"::"('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) Language.com" 
           ("_\<ggreater>\<^sub>s/ _" [22, 21] 21)
       "_FCall_s" :: "['p,actuals,idt,(('a,string,'f) Language.com)]\<Rightarrow> (('a,string,'f) Language.com)" 
                      ("CALL\<^sub>s __ \<ggreater> _./ _" [1000,1000,1000,21] 21)



translations
"_Bind_s e i c" == "CONST bind (_quote e) (\<lambda>i. c)"
"_FCall_s p acts i c" == "_FCall_s p acts (\<lambda>i. c)"
"_bseq_s c d" == "CONST bseq c d"



definition Let':: "['a, 'a => 'b] => 'b"
  where "Let' = Let"

ML_file "hoare_syntax_seq.ML"





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
 [(@{syntax_const "_Call_s"}, Hoare_Syntax.call_tr false false),
  (@{syntax_const "_FCall_s"}, Hoare_Syntax.fcall_tr),
  (@{syntax_const "_CallAss_s"}, Hoare_Syntax.call_ass_tr false false),
  (@{syntax_const "_GuardedCall_s"}, Hoare_Syntax.call_tr false true),
  (@{syntax_const "_GuardedCallAss_s"}, Hoare_Syntax.call_ass_tr false true),
  (@{syntax_const "_Proc_s"}, Hoare_Syntax.proc_tr),
  (@{syntax_const "_ProcAss_s"}, Hoare_Syntax.proc_ass_tr),
  (@{syntax_const "_DynCall_s"}, Hoare_Syntax.call_tr true false),
  (@{syntax_const "_DynCallAss_s"}, Hoare_Syntax.call_ass_tr true false),
  (@{syntax_const "_GuardedDynCall_s"}, Hoare_Syntax.call_tr true true),
  (@{syntax_const "_GuardedDynCallAss_s"}, Hoare_Syntax.call_ass_tr true true)]
*}

(*
  (@{syntax_const "_Call"}, Hoare_Syntax.call_ast_tr),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_ast_tr),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.guarded_call_ast_tr),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.guarded_call_ass_ast_tr)
*)

parse_translation {*
 [(@{syntax_const "_Assign_s"}, Hoare_Syntax.assign_tr),
  (@{syntax_const "_raise_s"}, Hoare_Syntax.raise_tr),
  (@{syntax_const "_New_s"}, Hoare_Syntax.new_tr),
  (@{syntax_const "_NNew_s"}, Hoare_Syntax.nnew_tr),
  (@{syntax_const "_GuardedAssign_s"}, Hoare_Syntax.guarded_Assign_tr),
  (@{syntax_const "_GuardedNew_s"}, Hoare_Syntax.guarded_New_tr),
  (@{syntax_const "_GuardedNNew_s"}, Hoare_Syntax.guarded_NNew_tr),
  (@{syntax_const "_GuardedWhile_inv_var_s"}, Hoare_Syntax.guarded_While_tr),
  (@{syntax_const "_GuardedWhileFix_inv_var_hook_s"}, Hoare_Syntax.guarded_WhileFix_tr),
  (@{syntax_const "_GuardedCond_s"}, Hoare_Syntax.guarded_Cond_tr),
  (@{syntax_const "_Basic_s"}, Hoare_Syntax.basic_tr)]
*}

parse_translation {*
 [(@{syntax_const "_Init_s"}, Hoare_Syntax.init_tr),
  (@{syntax_const "_Loc_s"}, Hoare_Syntax.loc_tr)] 
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
  let
    fun selector (Const (c,T)) = Hoare.is_state_var c  
      | selector _ = false;

    fun measure_tr' ctxt ((t as (Abs (_,_,p)))::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Measure"}) (t::ts)
          else raise Match
      | measure_tr' _ _ = raise Match

    fun mlex_tr' ctxt ((t as (Abs (_,_,p)))::r::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Mlex"}) (t::r::ts)
          else raise Match
      | mlex_tr' _ _ = raise Match

  in
   [(@{const_syntax measure}, measure_tr'),
    (@{const_syntax mlex_prod}, mlex_tr')]
  end
*}


print_translation {*
 [(@{const_syntax call}, Hoare_Syntax.call_tr'),
  (@{const_syntax dynCall}, Hoare_Syntax.dyn_call_tr'),
  (@{const_syntax fcall}, Hoare_Syntax.fcall_tr'),
  (@{const_syntax Call}, Hoare_Syntax.proc_tr')]
*}

end