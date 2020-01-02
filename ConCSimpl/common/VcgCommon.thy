theory VcgCommon
imports "../EmbSimpl/StateSpace" "HOL-Statespace.StateSpaceLocale" "../EmbSimpl/Generalise" "../EmbSimpl/HoareCon"
 
begin

definition list_multsel:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" (infixl "!!" 100)
  where "xs !! ns = map (nth xs) ns"

definition list_multupd:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "list_multupd xs ns ys = foldl (\<lambda>xs (n,v). xs[n:=v]) xs (zip ns ys)"

nonterminal lmupdbinds and lmupdbind

syntax
  \<comment> \<open>@ multiple list update \<close>
  "_lmupdbind":: "['a, 'a] => lmupdbind"    ("(2_ [:=]/ _)")
  "" :: "lmupdbind => lmupdbinds"    ("_")
  "_lmupdbinds" :: "[lmupdbind, lmupdbinds] => lmupdbinds"    ("_,/ _")
  "_LMUpdate" :: "['a, lmupdbinds] => 'a"    ("_/[(_)]" [900,0] 900)

translations
  "_LMUpdate xs (_lmupdbinds b bs)" == "_LMUpdate (_LMUpdate xs b) bs"
  "xs[is[:=]ys]" == "CONST list_multupd xs is ys"

text {* reverse application *}
definition rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr "|>" 60)
  where "rapp x f = f x"

nonterminal 
  bdy and
  newinit and
  newinits and
  grds and
  grd and
  locinit and
  locinits and
  basics and
  basic and
  basicblock and
  switchcase and
  switchcases 

syntax
  "_quote"       :: "'b => ('a => 'b)"
  "_antiquoteCur0"  :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_antiquoteCur"  :: "('a => 'b) => 'b"
  "_antiquoteOld0"  :: "('a => 'b) => 'a => 'b"       ("\<^bsup>_\<^esup>_" [1000,1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b" 
  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     ("(\<lbrace>_. _\<rbrace>)" [1000,0] 1000)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("_\<surd>" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("_#" [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       ("_" [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         ("_" 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" ("_,/ _" [999,1000] 1000)
  "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" ("(2\<acute>_ :==/ _)")
  ""             :: "newinit \<Rightarrow> newinits"    ("_")
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" ("_,/ _")
  "_locnoinit"    :: "ident \<Rightarrow> locinit"               ("\<acute>_")
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          ("(2\<acute>_ :==/ _)")
  ""             :: "locinit \<Rightarrow> locinits"             ("_")
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" ("_,/ _")
  "_BasicBlock":: "basics \<Rightarrow> basicblock" ("_")
  "_BAssign"   :: "'b => 'b => basic"    ("(_ :==/ _)" [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             ("_")
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" ("_,/ _")
  "_switchcasesSingle"  :: "switchcase \<Rightarrow> switchcases" ("_")         
  "_switchcasesCons":: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases"
                       ("_/ | _") 
syntax (ASCII)
  "_Assert"      :: "'a => 'a set"           ("({|_|})" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    ("({|_. _|})" [1000,0] 1000)

syntax (xsymbols)
  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     ("(\<lbrace>_. _\<rbrace>)" [1000,0] 1000)
  "_AssertR"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>\<^sub>r)" [0] 1000) 

translations
 "(_switchcasesSingle b)" => "[b]"
 "(_switchcasesCons b bs)" => "CONST Cons b bs"

parse_ast_translation \<open>
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) (map Ast.strip_positions asts)
  in
   [(@{syntax_const "_antiquoteCur0"}, K (tr @{syntax_const "_antiquoteCur"})),
    (@{syntax_const "_antiquoteOld0"}, K (tr @{syntax_const "_antiquoteOld"}))]
  end
\<close>

print_ast_translation \<open>
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) asts
  in
   [(@{syntax_const "_antiquoteCur"}, K (tr @{syntax_const "_antiquoteCur0"})),
    (@{syntax_const "_antiquoteOld"}, K (tr @{syntax_const "_antiquoteOld0"}))]
  end
\<close>

nonterminal par and pars and actuals

syntax 
  "_par" :: "'a \<Rightarrow> par"                                ("_")
  ""    :: "par \<Rightarrow> pars"                               ("_")
  "_pars" :: "[par,pars] \<Rightarrow> pars"                      ("_,/_")
  "_actuals" :: "pars \<Rightarrow> actuals"                      ("'(_')")
  "_actuals_empty" :: "actuals"                        ("'(')")

syntax
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_\<rightarrow>_" [65,1000] 100)

syntax (ASCII)
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_->_" [65,1000] 100)

translations 

 "p\<rightarrow>f"        =>  "f p"
 "g\<rightarrow>(_antiquoteCur f)" <= "_antiquoteCur f g" 
 "{|s. P|}"                   == "{|_antiquoteCur( (=) s) \<and> P |}"
 "{|b|}"                   => "CONST Collect (_quote b)" 


nonterminal modifyargs

syntax
  "_may_modify" :: "['a,'a,modifyargs] \<Rightarrow> bool" 
        ("_ may'_only'_modify'_globals _ in [_]" [100,100,0] 100)
  "_may_not_modify" :: "['a,'a] \<Rightarrow> bool"      
        ("_ may'_not'_modify'_globals _" [100,100] 100)
  "_may_modify_empty" :: "['a,'a] \<Rightarrow> bool"      
        ("_ may'_only'_modify'_globals _ in []" [100,100] 100)
  "_modifyargs" :: "[id,modifyargs] \<Rightarrow> modifyargs" ("_,/ _")
  ""            :: "id => modifyargs"              ("_")

translations
"s may_only_modify_globals Z in []" => "s may_not_modify_globals Z"
axiomatization NoBody::"('s,'p,'f) com" 

ML_file "hoare.ML"
ML_file "hoare_syntax.ML" 

parse_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val globalsN = "globals";
    val ex = @{const_syntax mex};
    val eq = @{const_syntax meq};
    val varn = Hoare_Con.varname;

    fun extract_args (Const (argsC,_)$Free (n,_)$t) = varn n::extract_args t
      | extract_args (Free (n,_)) = [varn n]
      | extract_args t            = raise TERM ("extract_args", [t])

    fun idx [] y = error "idx: element not in list"
     |  idx (x::xs) y = if x=y then 0 else (idx xs y)+1

    fun gen_update ctxt names (name,t) = 
        Hoare_Syntax_Common.update_comp ctxt [] false true name (Bound (idx names name)) t

    fun gen_updates ctxt names t = Library.foldr (gen_update ctxt names) (names,t) 

    fun gen_ex (name,t) = Syntax.const ex $ Abs (name,dummyT,t)
 
    fun gen_exs names t = Library.foldr gen_ex (names,t)

  
    fun tr ctxt s Z names =
      let val upds = gen_updates ctxt (rev names) (Syntax.free globalsN$Z);
          val eq   = Syntax.const eq $ (Syntax.free globalsN$s) $ upds;
      in gen_exs names eq end;

    fun may_modify_tr ctxt [s,Z,names] = tr ctxt s Z 
                                           (sort_strings (extract_args names))
    fun may_not_modify_tr ctxt [s,Z] = tr ctxt s Z []
  in
   [(@{syntax_const "_may_modify"}, may_modify_tr),
    (@{syntax_const "_may_not_modify"}, may_not_modify_tr)]
  end
\<close>

print_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val chop = Hoare_Con.chopsfx Hoare_Con.deco;

    fun get_state ( _ $ _ $ t) = get_state t  (* for record-updates*)
      | get_state ( _ $ _ $ _ $ _ $ _ $ t) = get_state t (* for statespace-updates *)
      | get_state (globals$(s as Const (@{syntax_const "_free"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_bound"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_var"},_) $ Var _)) = s
      | get_state (globals$(s as Const _)) = s
      | get_state (globals$(s as Free _)) = s
      | get_state (globals$(s as Bound _)) = s
      | get_state t              = raise Match;

    fun mk_args [n] = Syntax.free (chop n)
      | mk_args (n::ns) = Syntax.const argsC $ Syntax.free (chop n) $ mk_args ns
      | mk_args _      = raise Match;

    fun tr' names (Abs (n,_,t)) = tr' (n::names) t
      | tr' names (Const (@{const_syntax mex},_) $ t) = tr' names t  
      | tr' names (Const (@{const_syntax meq},_) $ (globals$s) $ upd) =
            let val Z = get_state upd;
                  
            in (case names of 
                  [] => Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
                | xs => Syntax.const @{syntax_const "_may_modify"} $ s $ Z $ mk_args (rev names))
            end;

    fun may_modify_tr' [t] = tr' [] t
    fun may_not_modify_tr' [_$s,_$Z] = Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
  in
    [(@{const_syntax mex}, K may_modify_tr'),
     (@{const_syntax meq}, K may_not_modify_tr')]
  end
\<close>

syntax
"_Measure":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
      ("MEASURE _" [22] 1)
"_Mlex":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
      (infixr "<*MLEX*>" 30)
"_to_quote":: "'b  \<Rightarrow> ('a \<Rightarrow> 'b)"
      ("quot _" [22] 1)

"_to_anti_quote":: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"
      ("antiquot _" [22] 1)

translations
 "MEASURE f"       => "(CONST measure) (_quote f)"
 "f <*MLEX*> r"       => "(_quote f) <*mlex*> r"
 "quot P"       => "(_quote P)"
 "antiquot P" =>  "(_antiquoteCur P)"

print_translation \<open>
  let
    fun selector (Const (c,T)) = Hoare_Con.is_state_var c  
      | selector _ = false;

    fun measure_tr' ctxt ((t as (Abs (_,_,p)))::ts) =
          if Hoare_Syntax_Common.antiquote_applied_only_to selector p
          then Hoare_Syntax_Common.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Measure"}) (t::ts)
          else raise Match
      | measure_tr' _ _ = raise Match

    fun mlex_tr' ctxt ((t as (Abs (_,_,p)))::r::ts) =
          if Hoare_Syntax_Common.antiquote_applied_only_to selector p
          then Hoare_Syntax_Common.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Mlex"}) (t::r::ts)
          else raise Match
      | mlex_tr' _ _ = raise Match

  in
   [(@{const_syntax measure}, measure_tr'),
    (@{const_syntax mlex_prod}, mlex_tr')]
  end
\<close>


parse_translation \<open>
  let
    fun quote_tr1 ctxt [t] = Hoare_Syntax_Common.quote_tr ctxt @{syntax_const "_antiquoteCur"} t
      | quote_tr1 ctxt ts = raise TERM ("quote_tr1", ts);
  in [(@{syntax_const "_quote"}, quote_tr1)] end
\<close>

parse_translation \<open>
 [(@{syntax_const "_antiquoteCur"},
    K (Hoare_Syntax_Common.antiquote_varname_tr @{syntax_const "_antiquoteCur"}))]
\<close>

parse_translation \<open>
 [(@{syntax_const "_antiquoteOld"}, Hoare_Syntax_Common.antiquoteOld_tr),
  (@{syntax_const "_BasicBlock"}, Hoare_Syntax_Common.basic_assigns_tr)]
\<close>  

end