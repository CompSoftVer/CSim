theory LanguageSafe
imports Main "../EmbSimpl/Semantic" "../EmbSimpl/HoarePartialDef" "../lib/sep_algebra/Separata"
             "../EmbSimpl/HoarePartialProps"
begin

definition fun_safe:: "('s::heap_sep_algebra \<Rightarrow> 's) \<Rightarrow> bool"
where 
"fun_safe f \<equiv> \<forall>h h1 h2 t. t = f h1 \<and> (h1, h2 \<triangleright> h) \<longrightarrow> (t, h2 \<triangleright>(f h))"

definition set_safe:: "('s::heap_sep_algebra \<times> 's) set \<Rightarrow> bool"
where
"set_safe s \<equiv> \<forall>h h1 h2 t.((h1, h2 \<triangleright> h) \<and> (h1,t)\<in>s) \<longrightarrow>
                            t##h2 \<and> (h,t + h2) \<in> s \<and> 
                            (\<forall>h'. (h,h')\<in>s \<longrightarrow> h' = (t+h2))"

definition guard_safe::"('s::heap_sep_algebra) set \<Rightarrow> bool"
where
"guard_safe g \<equiv> \<forall>h h1 h2 .(h1, h2 \<triangleright> h) \<and> ((h1\<in>g) \<longrightarrow> h\<in>g) \<and> (h1\<notin>g \<longrightarrow> h\<notin>g)"


definition cond_safe::"('s::heap_sep_algebra) set \<Rightarrow> ('s::heap_sep_algebra) set \<Rightarrow> bool"
where
"cond_safe b P \<equiv>\<forall>s'\<in>P. \<forall>s. s' \<preceq> s  \<longrightarrow> ((s \<in> b) =  (s'\<in>b))"

definition sep_alg_set_plus:: "('s::heap_sep_algebra) set \<Rightarrow> ('s::heap_sep_algebra) set \<Rightarrow> ('s::heap_sep_algebra) set" (infixr "\<Oplus>" 60) where
"A \<Oplus> B \<equiv> undefined"

primrec prog_safe:: "('s::heap_sep_algebra,'p,'f) com \<Rightarrow> ('s::heap_sep_algebra) set \<Rightarrow> 'f set \<Rightarrow> bool"
where
"prog_safe Skip P F = True" |
"prog_safe (Basic g) P F = fun_safe g" |
"prog_safe (Spec r) P F =  set_safe r" |
"prog_safe (Seq c\<^sub>1 c\<^sub>2) P F = (\<exists>P1 P2. P1 \<Oplus> P2 = P \<and> prog_safe c\<^sub>1 P1 F \<and> prog_safe c\<^sub>2 P2 F)" |
"prog_safe (Cond b c\<^sub>1 c\<^sub>2) P F =  (cond_safe b P \<and> prog_safe c\<^sub>1 P F \<and> prog_safe c\<^sub>2 P F)" |
"prog_safe (While b c) P F = (cond_safe b P \<and> prog_safe c P F)" |
"prog_safe (Call p) P F = True"|
"prog_safe (DynCom c) P F =  (\<forall>s. prog_safe (c s) P F)" |
"prog_safe (Guard f' g c) P F = (cond_safe g P \<and> prog_safe c P F)" |
"prog_safe Throw P F = True" |
"prog_safe (Catch c\<^sub>1 c\<^sub>2) P F = (prog_safe c\<^sub>1 P F \<and> prog_safe c\<^sub>2 P F)"

definition prog_env_safe:: "('s,'p,'f) body \<Rightarrow> ('s::heap_sep_algebra,'p,'f) com \<Rightarrow> 
('s::heap_sep_algebra) set \<Rightarrow> 'f set \<Rightarrow> bool"
where "prog_env_safe \<Gamma> c I\<^sub>s F \<equiv> 
prog_safe c I\<^sub>s F \<and> (\<forall>p c. \<Gamma> p = Some c \<longrightarrow> prog_safe c I\<^sub>s F)"

(*
lemma exec_program_safe_normal:
  assumes a0: "\<Gamma>\<turnstile>\<langle>c,Normal s1\<rangle> \<Rightarrow> Normal t1" and
          a2: "s1,s2 \<triangleright> s" and 
          a3: "prog_env_safe \<Gamma> c I F"
     shows "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Normal (t1+s2) \<and> (t1##s2)"
using a0 a2 a3
proof (induct arbitrary:s s1 s2 t1)
  case (Skip ss) 
    then have t1_s1:"t1 = s1" 
      
      sorry
    then have "\<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow> Normal s" using exec.Skip by fastforce
    then show ?case 
      using Skip t1_s1 unfolding tern_rel_def by fastforce    
next
  case (Spec s1' t1' r) 
  have "(s,t1+s2)\<in>r \<and> t1##s2" using Spec(1) Spec(3) Spec(2) Spec(4) 
    unfolding prog_env_safe_def prog_safe.simps(3) set_safe_def
    tern_rel_def by blast
  thus ?case using exec.Spec by auto 
next 
  case (SpecStuck) thus ?case by auto
next 
  case (FaultProp) thus ?case by auto
next
  case (Guard sa g c ta f)  
  then have " \<Gamma>\<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Normal (t1 + s2) \<and> t1 ## s2 \<and> s\<in>g" 
    unfolding prog_env_safe_def prog_safe.simps(9) guard_safe_def by blast
  thus ?case using exec.Guard by fastforce
next
  case (GuardFault sa g f ta s) thus ?case by auto
next
  case (Basic f sa) thus ?case 
    unfolding prog_env_safe_def prog_safe.simps(2) fun_safe_def
              tern_rel_def
    using exec.Basic xstate.inject(1) 
    by metis
next
  case (Seq c1 sc1 s' c2 t) thus ?case 
   unfolding tern_rel_def prog_env_safe_def prog_safe.simps(4)  sorry
next
  case (CondTrue) thus ?case sorry
next
  case (CondFalse) thus ?case sorry
next
  case (WhileTrue) thus ?case sorry
next
  case (WhileFalse) thus ?case sorry
next
  case (Call) thus ?case sorry
next
  case (CallUndefined) thus ?case sorry
next
  case (StuckProp) thus ?case sorry
next
  case (DynCom) thus ?case sorry
next
  case (Throw) thus ?case sorry
next
  case (CatchMatch) thus ?case sorry
next
  case (CatchMiss) thus ?case sorry 
qed (auto)

lemma exec_program_safe_fault:
  assumes a0: "\<Gamma>\<turnstile>\<langle>c,Normal s1\<rangle> \<Rightarrow> Abrupt t1" and
          a1: "t1 \<uplus>\<^sub>s s2" and
          a2: "prog_env_safe \<Gamma> c"
     shows "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Abrupt (t1+s2)"
sorry

lemma exec_program_safe_Stuck:
  assumes a0: "\<Gamma>\<turnstile>\<langle>c,Normal s1\<rangle> \<Rightarrow> Stuck" and
          a1: "t1 \<uplus>\<^sub>s s2" and
          a2: "prog_env_safe \<Gamma> c"
     shows "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Stuck"
sorry

lemma exec_program_safe_Fault:
  assumes a0: "\<Gamma>\<turnstile>\<langle>c,Normal s1\<rangle> \<Rightarrow> Fault f" and
          a1: "t1 \<uplus>\<^sub>s s2" and
          a2: "prog_env_safe \<Gamma> c"
     shows "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> Fault f"
sorry 

inductive_cases satis_elim_case [cases set]:
"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P Seq c1 c2 Q,A"
*)

lemma star_left_lem:"(P ** R) s \<Longrightarrow> \<exists>sp sr. (sp,sr\<triangleright>s) \<and> P sp \<and> R sr"
by separata

lemma "(sp,sr\<triangleright>s) \<Longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> = n \<Rightarrow> Normal s' \<Longrightarrow> prog_env_safe \<Gamma> c I F \<Longrightarrow>
\<Gamma>\<turnstile>\<langle>c,Normal sp\<rangle> = n \<Rightarrow> Normal t' \<and>  (t',sr\<triangleright>s')"
sorry

lemma "(sp,sr\<triangleright>s) \<Longrightarrow> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> = n \<Rightarrow> Abrupt s' \<Longrightarrow> prog_env_safe \<Gamma> c I F \<Longrightarrow>
\<Gamma>\<turnstile>\<langle>c,Normal sp\<rangle> = n \<Rightarrow> Abrupt t' \<and>  (t',sr\<triangleright>s')"
sorry

lemma prog_env_safe_seq: "prog_env_safe \<Gamma> (Seq c1 c2) I\<^sub>s F \<Longrightarrow> 
  prog_env_safe \<Gamma> c1 I\<^sub>s F \<and> prog_env_safe \<Gamma> c2 I\<^sub>s F"
unfolding prog_env_safe_def 
by auto

lemma post_cond_safe: "P \<subseteq> I\<^sub>s \<Longrightarrow> \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A \<Longrightarrow> 
(\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A) \<Longrightarrow> 
(\<forall>s t. \<Gamma>\<turnstile>\<langle>c,s \<rangle> =n\<Rightarrow> t \<longrightarrow> s \<in> Normal ` P \<longrightarrow> t \<notin> Fault ` F) \<Longrightarrow>
Q \<subseteq> I\<^sub>s"
sorry

(*declare [[show_types]]*)
text {*
  We introduce separation logic as a layer on top of Simpl. Separation Logic needs assertions to be 
  restricted by means of the syntax. The most important rule in Separation Logic, the Frame Rule,
  allows to reason on separated resources, allowing to scale verification. The Frame Rule says 
  {P} c {Q} \Longarrow {P*R} c {Q*R} where no variable occurring free in R is modified by c. 
  Simpl is a language with a minimal syntax, which makes difficult to deploy separation logic in it. 
  However, it is possible to add separation logic on top of Simpl adding conditions to the frame 
  rule to ensure this (a). 
  We use the separation algebra library to model Simpl's separation logic. Using this it is possible
  to have separation on structures like records,  that are not commonly used to represent the 
  state in separation logic. If we use the record structure as an example, to be able to consider 
  a record as a separation algebra we need that its fields are also separation algebras. Then, 
  two variables $r1, r2$ with type record $r$  will be disjoints if for each field $f$ in the $r$ 
  $f r1$ and $f r2$ are separated. And we consider that $r1$ with type record $r$ is empty ($\<emptyset>$) 
  if for each every $f$ in $r$, $f r1 = \<emptyset>$ . Finally we merge (+) two disjoints variables $r1, r2$
  into a new record $rn$ merging every field $f1 \<cdots> fn$ in $r1, r2$, and 
  $rn = (| f1= f1 r1 + f1 r2, \<cdots> fn = fn r1 + fn r2 |). However, Simpl rules to change the state 
  can modify a field breaking separation (for example, can make $\<emptyset>$ a non-empty field, or vice-verse).
  (b).

  In our specification, we consider a static state, where it is not possible to create or remove
  new variables. It is possible still create dynamic behaviour adding control structures. This is not
  a limitation indeed, since memory is not an infinite resource and we always start from a finite
  set of memory positions. In order to overcome (a) and (b) we need to consider some assumptions.
  
  For (a), First, we use two predicates $I_t, I_c$ where $I_t$ constrains the state in such a way that all
  its fields are non-empty, and $I_c$ constrains the state to the states where variables in a program
  are accessed are non-empty. Finally we express (a) saying that R has to be included in $I_t - I_c$
  $I_c$ and $I_t$ are part of the specification and can be calculated through program analysis and 
  program annotations.

  For (b), we need to use a predicate prog_env_safe, to control that operations changing the state
  does not include new variables. Also, in the case of branches, that the condition of the branch
  does not references variables out of $I_c$ and that can make change the behaviour of the program
  for a bigger state.
  
  $I_c$ is a nexus between the syntax restricted predicates in original separation logic and
  and the absence of a restricted syntax in Simpl. But we still need some additional information
  about the program and $I_c$. For example, a composed statement c=c1;c2, $I_c$ is the combination
  of $I_c1$ and $I_c2$, which respectively represent the variables invariant in $c1$ and $c2$. 
  And it should express that field $f$ is non-empty in $I_c$ if $f$ is non-empty in $I_c1$ or is 
  non-empty in $I_c2$. This will also be necessary for other constructors like conditional branching, 
  and while, very likely having to include the guard of these statements. 
  However, we don't have a way of expressing that since we don't have a syntax.
  To fill this gap, we require that the state has to be of a "domain" class, which provides functions
  to extract the variable domain of a state (e.g., for a record will be the record's fields), and
  to obtain the value of a variable, (perhaps also to set the value). Since in Isabelle/HOL
  functions are not polymorphic, and fields of a record may have different types,
  the function obtaining/setting a value must have a data type collecting the types of a variable.
  It is possible therefore to define an isomorphism between the state and the values of the values
  of variables belonging to the domain of the state (very likely this isomorphism will help in the 
  proof of soundness of the frame rule).  
*}

lemma frame_safe_program:
  assumes a0: "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A" and 
    a1: "prog_env_safe \<Gamma> c I\<^sub>s F" and
    a2: "\<forall>s t. s\<in>I\<^sub>s \<and> t\<in>I\<^sub>t \<longrightarrow> s \<preceq> t" and
    a3: "R\<subseteq>I\<^sub>t - I\<^sub>s"
  shows "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> (fun_set ((set_fun P) \<and>* (set_fun R))) c (fun_set ((set_fun Q) \<and>* (set_fun R))),(fun_set ((set_fun A) \<and>* (set_fun R)))"
proof-
{fix n
 have "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> (fun_set ((set_fun P) \<and>* (set_fun R))) c (fun_set ((set_fun Q) \<and>* (set_fun R))),(fun_set ((set_fun A) \<and>* (set_fun R)))"
proof (rule cnvalidI)
  {fix s t 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t"   
  assume P: "s \<in> (fun_set ((set_fun P) \<and>* (set_fun R)))"
  assume t_notin_F: "t \<notin> Fault ` F"
  obtain st where s_normal: "(st::('b, 'c) xstate)=Normal s" by auto
  then have exec: "\<Gamma>\<turnstile>\<langle>c,st\<rangle> =n\<Rightarrow> t" using exec by auto
  then have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A" using a0 by (simp add: hoare_complete')
  then have a0:"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A" using a0 by auto
  obtain sp sr where s_split: "(sp,sr\<triangleright>s) \<and> sp \<in> (fun_set (set_fun P)) \<and> sr \<in> (fun_set (set_fun R))"
    using P star_left_lem by fastforce
  show "t \<in> Normal ` (fun_set ((set_fun Q) \<and>* (set_fun R))) \<union> Abrupt ` (fun_set ((set_fun A) \<and>* (set_fun R)))" 
  using exec s_normal P a0 t_notin_F a1 ctxt s_split a2 a3 
  proof (induct arbitrary: s P Q A R sp sr)
    case (Skip t n)
    then have t:"t=s" by auto
    then have "\<Gamma>\<turnstile>\<langle>Skip,Normal s\<rangle> =n\<Rightarrow> Normal s" using execn.Skip by fastforce    
    obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1,s2\<triangleright>s)"
      using Skip(2)
      by (metis mem_Collect_eq sep_conj_def tern_rel_def) 
    then have s1_p: "s1\<in>P" by auto
    have step:"\<Gamma>\<turnstile>\<langle>Skip,Normal s1\<rangle> =n\<Rightarrow> Normal s1"
      using execn.Skip by fastforce 
    have s1_notin_f:"Normal s1 \<notin> Fault ` F" by fastforce
    have "Normal s1 \<in> Normal ` Q \<union> Abrupt ` A" using cnvalidD[OF Skip(3)[rule_format] Skip(6) step s1_p s1_notin_f]
      by auto      
    then have "s1\<in>Q" by auto       
    then show ?case using P_s1 t
      by (metis UnCI image_eqI mem_Collect_eq sep_conj_def tern_rel_def)              
  next  
    case (Basic f sa n) 
    then have t:"sa=s" by auto
    have safe_basic:"\<forall>h h1 h2 t. t = f h1 \<and> (h1,h2\<triangleright>h) \<longrightarrow> (t,h2\<triangleright>(f h))" 
      using Basic.prems(5) unfolding prog_env_safe_def prog_safe.simps(2) fun_safe_def by auto
    then obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1,s2\<triangleright>s)" using Basic(2)
        by (metis (full_types) mem_Collect_eq sep_conj_def tern_rel_def)
    then have s1_p:"s1\<in> P " by auto
    then have step:"\<Gamma>\<turnstile>\<langle>Basic f,Normal s1\<rangle>=n\<Rightarrow> Normal (f s1)" 
        using execn.Basic P_s1 by meson
    have s1_notin_f:"Normal (f s1) \<notin> Fault ` F" by fastforce
    have "Normal (f s1) \<in> Normal ` Q \<union> Abrupt ` A" using cnvalidD[OF Basic(3)[rule_format] Basic(6) step s1_p s1_notin_f]
      by auto
    then have "(f s1) \<in> Q" by auto
    also have "(f s1)## s2 \<and> ((f s1)+s2 = f s)" using safe_basic P_s1
      by (simp add: tern_rel_def)       
    ultimately show ?case using P_s1 t 
      unfolding sep_conj_def by fastforce
  next
    case (Spec sa t r n)
    then have step_spec:"\<Gamma>\<turnstile> \<langle>Spec r,Normal s\<rangle> =n\<Rightarrow> Normal t" using execn.Spec by auto
    then obtain tt where tt:"(tt::('b, 'c) xstate)=Normal t" by auto
    then have "sa=s" using Spec by auto
    have safe_spec: "\<forall>h h1 h2 t.((h1,h2\<triangleright>h) \<and> (h1,t)\<in>r) \<longrightarrow>
                            t##h2 \<and> (h,t + h2) \<in> r \<and> 
                            (\<forall>h'. (h,h')\<in>r \<longrightarrow> h' = (t+h2))" 
      using Spec.prems(5) unfolding prog_env_safe_def prog_safe.simps(3) set_safe_def by auto
    then obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1,s2\<triangleright>s)" using Spec(3)
        by (metis (full_types) mem_Collect_eq sep_conj_def tern_rel_def)
    then have s1_p:"s1\<in> P" by auto    
    have "\<exists>t. (s1,t)\<in>r" 
    proof -
    {assume "\<forall>t. (s1,t)\<notin>r"
     then have step:"\<Gamma>\<turnstile> \<langle>Spec r,Normal s1\<rangle> =n\<Rightarrow> Stuck" by (fastforce intro: execn.SpecStuck)
     then have Stuck_notin_F:"Stuck\<notin>Fault ` F" by auto
     have False using cnvalidD[OF Spec(4)[rule_format] Spec(7) step s1_p Stuck_notin_F]
       by auto
    } thus ?thesis by auto qed
    then obtain t1 where s1_t1_r:"(s1,t1)\<in>r" by auto
    then have stepp1:"\<Gamma>\<turnstile>\<langle>Spec r,Normal s1\<rangle> =n\<Rightarrow> Normal t1"
      using execn.Spec by fastforce 
    then have Normals1_notin_F:"Normal t1\<notin>Fault ` F" by auto    
    then have t1_q:"(t1) \<in> Q" using cnvalidD[OF Spec(4)[rule_format] Spec(7) stepp1 s1_p Normals1_notin_F] by auto
    have s_t1_s2_r:"t1##s2 \<and>(s,t1 + s2)\<in> r" using safe_spec P_s1 s1_t1_r 
      unfolding tern_rel_def by fastforce
    also then have "\<Gamma>\<turnstile> \<langle>Spec r,Normal s\<rangle> =n\<Rightarrow> Normal (t1+s2)"  by (fastforce intro: execn.Spec)
    ultimately have "tt =Normal (t1+s2)"
      using tt safe_spec step_spec  P_s1 execn_Normal_elim_cases(7) s1_t1_r
       by (metis execn_Normal_elim_cases(7)  tern_rel_def)
    then show ?case 
      using tt P_s1 s_t1_s2_r t1_q unfolding  sep_conj_def by fastforce    
  next        
    case (Seq c1 s1 n s1' c2 t)     
    (* then have step_seq:"\<Gamma>\<turnstile> \<langle>Seq c1 c2,Normal s1\<rangle> = n \<Rightarrow> t" using execn.Seq by auto
    have valid:"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P Seq c1 c2 Q,A" using Seq.prems(3) by auto    
    then obtain s' where stepc1:"\<Gamma>\<turnstile>\<langle>c1,Normal s\<rangle> =n\<Rightarrow>  s'" and stepc2:"\<Gamma>\<turnstile>\<langle>c2,s'\<rangle> =n\<Rightarrow>  t"   
      using Seq.hyps(1) Seq.hyps(3) Seq.prems(1)   
      by metis  
    obtain s'na where "s' = Normal s'na \<or> s' = Abrupt s'na"
      using valid unfolding cnvalid_def nvalid_def
    then obtain sna where "s' = Normal sna \<or> s' = Abrupt sna"
      
    then obtain Q' A' where c1valid:"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c1 Q',A'"
    proof -
      
    qed  
    have "s1' \<in> Normal ` {a. ((\<lambda>v. v \<in> Q') \<and>* (\<lambda>v. v \<in> R)) a} \<union> Abrupt ` {a. ((\<lambda>v. v \<in> A') \<and>* (\<lambda>v. v \<in> R)) a}"
    proof-
      have "s1' \<notin> Fault ` F" using c1valid Seq(10) Seq(1) unfolding cnvalid_def cvalid_def nvalid_def
        apply simp
        sorry
      then show ?thesis using Seq(2)[OF Seq(5) Seq(6) c1valid] sorry
    qed *)      
    have safe1: "prog_env_safe \<Gamma> c1 I\<^sub>s F" and safe2: "prog_env_safe \<Gamma> c2 I\<^sub>s F"
      using Seq(9) prog_env_safe_seq apply blast
      using Seq(9) prog_env_safe_seq by blast
    obtain I A' where small_state_exec1: "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c1 I,A'" sorry 
    obtain si where inter_big_state: "s1' = Normal si" sorry
    then have inter_big_cond: "si \<in> {a. ((\<lambda>v. v \<in> I) \<and>* (\<lambda>v. v \<in> R)) a}" sorry  
    then obtain si' where inter_big_cond_tern: "(si',sr\<triangleright>si) \<and> si' \<in> {\<sigma>. \<sigma> \<in> I} \<and> sr \<in> {\<sigma>. \<sigma> \<in> R}" sorry    
    then have small_state_exec2: "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> I c2 Q,A" sorry
    have inter_cond_safe: "I \<subseteq> I\<^sub>s" sorry
    show ?case using Seq(4)[OF inter_big_state inter_big_cond small_state_exec2 Seq(8) 
      safe2 Seq(10) inter_big_cond_tern Seq(12) inter_cond_safe Seq(14)] by auto
  next
    case Guard thus ?case sorry
  next
    case GuardFault thus ?case sorry
  next
    case FaultProp thus ?case sorry
  next
    case SpecStuck thus ?case sorry
  next
    case (CondTrue sa b c1 n t c2) thus ?case sorry
  next
    case CondFalse thus ?case sorry
  next
    case WhileTrue thus ?case sorry
  next
    case WhileFalse thus ?case sorry
  next
    case Call thus ?case sorry
  next
    case CallUndefined thus ?case sorry
  next
    case StuckProp thus ?case sorry
  next 
    case DynCom thus ?case sorry
  next
    case Throw thus ?case sorry
  next
    case AbruptProp thus ?case sorry
  next
    case CatchMatch thus ?case sorry
  next 
    case CatchMiss thus ?case sorry
  qed
 } qed
 
} thus ?thesis by auto


oops

(*
lemma frame_safe_program:
  assumes a0:
    "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> P c Q,A" and 
    a1:"prog_env_safe \<Gamma> c F"
  shows "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F\<^esub> (P\<and>*\<^sub>sR) c   (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
proof (rule cnvalidI)
  {fix s t 
  assume ctxt: "\<forall>(P, p, Q, A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A"
  assume exec: "\<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> =n\<Rightarrow> t" 
  assume P: "s \<in> (P\<and>*\<^sub>sR)"
  assume t_notin_F: "t \<notin> Fault ` F"
  then have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A" using a0 by (simp add: hoare_complete')
  show "t \<in> Normal ` (Q\<and>*\<^sub>sR) \<union> Abrupt ` (A\<and>*\<^sub>sR)"
  using exec P a0 t_notin_F a1
  proof (induct c arbitrary: s t P Q A R)
    case (Skip) 
    then have t:"t=Normal s"
      by (meson execn_Normal_elim_cases(4))
    then obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1 \<uplus>\<^sub>s s2)" 
      using Skip(2)
      by (metis mem_Collect_eq sep_conj_def sep_split1_def)    
    then have s1_p:"s1\<in> P " by auto
    have step:"\<Gamma>\<turnstile>\<langle>Skip,Normal s1\<rangle> =n\<Rightarrow> Normal s1"
      using execn.Skip by fastforce 
    have s1_notin_f:"Normal s1 \<notin> Fault ` F" by fastforce
    have "Normal s1 \<in> Normal ` Q \<union> Abrupt ` A" using cnvalidD[OF Skip(3)[rule_format] ctxt step s1_p s1_notin_f]
      by auto
    then have "s1\<in>Q" by auto
    then show ?case using P_s1 t
      by (metis UnCI image_eqI mem_Collect_eq sep_conj_def sep_split1_def)      
  next  
    case (Basic f)
    then have t:"t=Normal (f s)"
      by (meson execn_Normal_elim_cases(6))
    have safe_basic:"\<forall>h h1 h2 t. t = f h1 \<and> ((h1 \<uplus>\<^sub>p h2) h) \<longrightarrow> (t \<uplus>\<^sub>p h2) (f h)" 
      using Basic.prems(5) unfolding prog_env_safe_def prog_safe.simps(2) fun_safe_def by auto
    then obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1 \<uplus>\<^sub>s s2)" using Basic(2)
        by (metis (full_types) mem_Collect_eq sep_conj_def sep_split1_def)
    then have s1_p:"s1\<in> P " by auto
    then have step:"\<Gamma>\<turnstile>\<langle>Basic f,Normal s1\<rangle>=n\<Rightarrow> Normal (f s1)" 
        using execn.Basic P_s1 by meson
    have s1_notin_f:"Normal (f s1) \<notin> Fault ` F" by fastforce
    have "Normal (f s1) \<in> Normal ` Q \<union> Abrupt ` A" using cnvalidD[OF Basic(3)[rule_format] ctxt step s1_p s1_notin_f]
      by auto
    then have "(f s1) \<in> Q" by auto
    also have "(f s1)## s2 \<and> ((f s1)+s2 = f s)" using safe_basic P_s1 
         unfolding sep_disj_union_def sep_split1_def sep_split_def by fastforce
     ultimately show ?case 
        using P_s1 t unfolding sep_disj_union_def sep_split1_def sep_conj_def by fastforce
  next
    case (Spec r)
    have safe_spec: "\<forall>h h1 h2 t.(((h1 \<uplus>\<^sub>p h2) h) \<and> (h1,t)\<in>r) \<longrightarrow>
                            t##h2 \<and> (h,t + h2) \<in> r \<and> 
                            (\<forall>h'. (h,h')\<in>r \<longrightarrow> h' = (t+h2))" 
      using Spec.prems(5) unfolding prog_env_safe_def prog_safe.simps(3) set_safe_def by auto
    then obtain s1 s2 where P_s1:"((P)\<^sub>f s1) \<and> ((R)\<^sub>f s2) \<and> (s1 \<uplus>\<^sub>s s2)" using Spec(2)
        by (metis (full_types) mem_Collect_eq sep_conj_def sep_split1_def)
    then have s1_p:"s1\<in> P" by auto    
    have "\<exists>t. (s1,t)\<in>r" 
    proof -
    {assume "\<forall>t. (s1,t)\<notin>r"
     then have step:"\<Gamma>\<turnstile> \<langle>Spec r,Normal s1\<rangle> =n\<Rightarrow> Stuck" by (fastforce intro: execn.SpecStuck)
     then have Stuck_notin_F:"Stuck\<notin>Fault ` F" by auto
     have False using cnvalidD[OF Spec(3)[rule_format] ctxt step s1_p Stuck_notin_F]
       by auto
    } thus ?thesis by auto qed
    then obtain t1 where s1_t1_r:"(s1,t1)\<in>r" by auto
    then have stepp1:"\<Gamma>\<turnstile>\<langle>Spec r,Normal s1\<rangle> =n\<Rightarrow> Normal t1"
      using execn.Spec by fastforce 
    then have Normals1_notin_F:"Normal t1\<notin>Fault ` F" by auto
    have "Normal t1 \<in> Normal ` Q \<union> Abrupt ` A"using cnvalidD[OF Spec(3)[rule_format] ctxt stepp1 s1_p Normals1_notin_F]
      by auto
    then have t1_q:"(t1) \<in> Q" by auto
    have s_t1_s2_r:"t1##s2 \<and>(s,t1 + s2)\<in> r" using safe_spec P_s1 s1_t1_r 
      unfolding sep_split1_def sep_split_def sep_disj_union_def by fastforce
    also then have "\<Gamma>\<turnstile> \<langle>Spec r,Normal s\<rangle> =n\<Rightarrow> Normal (t1+s2)"  by (fastforce intro: execn.Spec)
    ultimately have "t =Normal (t1+s2)" 
      using  safe_spec  Spec.prems(1) P_s1  execn_Normal_elim_cases(7) s1_t1_r sep_split1_def sep_substate_disj_add substate_exists_split  
      by (metis )
    then show ?case 
      using P_s1 s_t1_s2_r t1_q unfolding  sep_disj_union_def sep_split1_def sep_conj_def by fastforce      
  next        
    case (Seq c1 c2)
      thus ?case
  } thus ?thesis by auto
qed *)

(*
lemma frame_safe_program:
  assumes a0:
    "\<forall>s t t'. P s \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t \<and> (t=Normal t' \<or> t=Abrupt t') \<longrightarrow> Q t'" and 
    a1:"prog_env_safe \<Gamma> c F"
  shows "\<forall>s t t'.  (P\<and>*R) s \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t \<and> (t=Normal t' \<or> t=Abrupt t') \<longrightarrow> (Q\<and>*R) t'"
proof -
  {fix s t t'
  assume a01:"(P\<and>*R) s \<and> \<Gamma>\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t  \<and> (t=Normal t' \<or> t=Abrupt t') "
  then have "((Q\<and>*R) t')"
  using a0 a1 
  proof(induct c)    
    case Skip 
    then have t:"t=Normal s"
      by (meson exec_Normal_elim_cases(4))
    then obtain s1 s2 where P_s1:"P s1 \<and> R s2 \<and> (s1 \<uplus>\<^sub>s s2)" using Skip(1)
      by (metis (full_types) sep_conj_def sep_split1_def)
    then have "\<Gamma>\<turnstile>\<langle>Skip,Normal s1\<rangle> \<Rightarrow> Normal s1"
      using exec.Skip by auto
    then have "(\<exists>t'. (Normal s1=Normal t' \<or> Normal s1=Abrupt t') \<and> Q t')"
      using Skip P_s1  by blast   
    then have "Q s1" by fastforce
    then show ?thesis using P_s1 t
      by (metis a01 sep_conjI sep_split1_def xstate.distinct(1) xstate.inject(1))     
  next
    case (Basic f)
      then have t:"t=Normal (f s) \<and> t' = (f s)" using exec_Normal_elim_cases(6)
        by (metis (no_types) xstate.inject(1) xstate.simps(5)) 
      have safe_basic:"\<forall>h h1 h2 t. t = f h1 \<and> ((h1 \<uplus>\<^sub>p h2) h) \<longrightarrow> (t \<uplus>\<^sub>p h2) (f h)" 
        using Basic.prems(3)  unfolding prog_env_safe_def prog_safe.simps(2) fun_safe_def by auto
      then obtain s1 s2 where P_s1:"P s1 \<and> R s2 \<and> (s1 \<uplus>\<^sub>s s2)" using Basic(1)
        by (metis (full_types) sep_conj_def sep_split1_def)
      then have "\<Gamma>\<turnstile>\<langle>Basic f,Normal s1\<rangle> \<Rightarrow> Normal (f s1)" 
        using exec.Basic by meson
      then have "(\<exists>t'. (Normal (f s1)=Normal t' \<or> Normal (f s1)=Abrupt t') \<and> Q t')"      
      using Basic P_s1  by blast   
      then have "Q (f s1)" by fastforce
      also have "(f s1)## s2 \<and> ((f s1)+s2 = f s)" using safe_basic P_s1 
         unfolding sep_disj_union_def sep_split1_def sep_split_def by fastforce
      ultimately show ?thesis 
        using P_s1 t unfolding sep_disj_union_def sep_split1_def sep_conj_def by fastforce
  next        
    case (Spec x)
      then have t:"(s,t') \<in> x \<and> t=Normal t'"
        using exec_Normal_elim_cases(7) xstate.distinct(1) 
              xstate.distinct(9) xstate.inject(1) xstate.simps(9) by metis
      have safe_basic:"\<forall>h h1 h2 t. (h1,t)\<in>x \<and> ((h1 \<uplus>\<^sub>p h2) h) \<longrightarrow> (h,t \<uplus> h2) \<in> x" 
        using Spec.prems(3)  unfolding prog_env_safe_def prog_safe.simps(3) set_safe_def by auto
      obtain s1 s2 where P_s1:"P s1 \<and> R s2 \<and> (s1 \<uplus>\<^sub>s s2)" using Spec(1)
        by (metis (full_types) sep_conj_def sep_split1_def)
      then have "\<Gamma>\<turnstile>\<langle>Spec x,Normal s1\<rangle> \<Rightarrow> Normal (f s1)" 
        using exec.Spec by meson
      then have "(\<exists>t'. (Normal (f s1)=Normal t' \<or> Normal (f s1)=Abrupt t') \<and> Q t')"      
      using Basic P_s1  by blast   
      then have "Q (f s1)" by fastforce
      also have "(f s1)## s2 \<and> ((f s1)+s2 = f s)" using safe_basic P_s1 
         unfolding sep_disj_union_def sep_split1_def sep_split_def by fastforce
      ultimately show ?thesis 
        using P_s1 t unfolding sep_disj_union_def sep_split1_def sep_conj_def by fastforce
  } thus ?thesis by auto
qed 
oops
*)

lemma if_der: assumes 
      a1:"\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>((P \<inter> b) \<and>*\<^sub>s R) c\<^sub>1 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)" and
      a1':"\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>(P \<inter> b) c\<^sub>1 Q,A" and
      a2:"\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>((P \<inter> -b) \<and>*\<^sub>s R) c\<^sub>2 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)" and 
      a2':"\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>(P \<inter> -b) c\<^sub>2 Q,A" and
      a3: "prog_env_safe \<Gamma> (Cond b c\<^sub>1 c\<^sub>2) F" and
      a4: "(pred_sep_domain b) \<subseteq> (pred_sep_domain P)"
 shows
    "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>(P \<and>*\<^sub>s R) (Cond b c\<^sub>1 c\<^sub>2) (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
 proof -{
    fix n
    have "\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>(P \<and>*\<^sub>s R) (Cond b c\<^sub>1 c\<^sub>2) (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)" 
    proof -
    {assume a0:"(\<forall>(P,p,Q,A)\<in>\<Theta>. \<Gamma>\<Turnstile>n:\<^bsub>/F\<^esub> P (Call p) Q,A)"
    then have "\<Gamma> \<Turnstile>n:\<^bsub>/F\<^esub> (P \<and>*\<^sub>s R) (Cond b c\<^sub>1 c\<^sub>2) (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
    proof -
       {fix s t
       assume  a00:"\<Gamma>\<turnstile>\<langle>Cond b c\<^sub>1 c\<^sub>2 ,s \<rangle> =n\<Rightarrow> t"
       assume  a11:"s \<in> Normal ` (P \<and>*\<^sub>s R)" 
       assume a22:"t \<notin> Fault ` F"               
       have a1:"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>((P \<inter> b) \<and>*\<^sub>s R) c\<^sub>1 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
         using a1 by auto
       then have a2:"\<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>((P \<inter> -b) \<and>*\<^sub>s R) c\<^sub>2 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
         using a2 by auto
       obtain s' where sep:"s=Normal s' \<and> s' \<in> (P \<and>*\<^sub>s R)" 
         using a11 by fastforce  
       then have "t \<in>  Normal ` (Q\<and>*\<^sub>sR) \<union> Abrupt `(A\<and>*\<^sub>sR)"
       proof (cases "s'\<in>b")
         case True
         then have step:"\<Gamma>\<turnstile>\<langle>c\<^sub>1,Normal s'\<rangle> =n\<Rightarrow> t"            
         proof -
           have "\<Gamma>\<turnstile> \<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s'\<rangle> =n\<Rightarrow> t"
            using a00 sep by auto
           then show ?thesis using True 
             by (meson execn_Normal_elim_cases(9))            
         qed           
         then have "s' \<in> (P \<and>*\<^sub>s R) \<inter> b" 
           using sep  True by auto
         obtain s1 s2 where sep:"s1 ## s2 \<and> s' = s1 + s2 \<and> s1\<in>P \<and> s2\<in>R "       
           by (metis mem_Collect_eq sep sep_conjE)
         then have "s1 \<preceq> s'" using sep_substate_def by fastforce
         then have "s1\<in>b" using True a4 a3 
           unfolding prog_env_safe_def prog_safe.simps cond_safe_def 
         by auto
         then have pre:"s' \<in> ((P \<inter> b) \<and>*\<^sub>s R)" 
           using sep unfolding sep_conj_def by auto          
         then have "t \<in> Normal ` (Q\<and>*\<^sub>sR) \<union> Abrupt `  (A\<and>*\<^sub>sR)"
           using cnvalidD[OF a1 a0 step pre a22] by auto
         thus ?thesis by auto
       next
         case False
         then have step:"\<Gamma>\<turnstile>\<langle>c\<^sub>2,Normal s'\<rangle> =n\<Rightarrow> t"   
         proof -
           have "\<Gamma>\<turnstile> \<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s'\<rangle> =n\<Rightarrow> t"
            using a00 sep by auto
           then show ?thesis using False 
             by (meson execn_Normal_elim_cases(9))            
         qed         
         obtain s1 s2 where sep:"s1 ## s2 \<and> s' = s1 + s2 \<and> s1\<in>P \<and> s2\<in>R "       
           by (metis mem_Collect_eq sep sep_conjE)
         then have "s1 \<preceq> s'" using sep_substate_def by fastforce
         then have "s1\<in>-b" using False a4 a3 
           unfolding prog_env_safe_def prog_safe.simps cond_safe_def 
         by auto
         then have pre:"s' \<in> ((P \<inter> -b) \<and>*\<^sub>s R)" 
           using sep unfolding sep_conj_def by auto  
         then have "t \<in> Normal ` (Q\<and>*\<^sub>sR) \<union> Abrupt `  (A\<and>*\<^sub>sR)"
           using cnvalidD[OF a2 a0 step pre a22] by auto
         thus ?thesis by auto
       qed } 
     then have ?thesis using nvalid_def by metis 
  thus ?thesis by auto
  qed 
  } thus ?thesis using cnvalid_def by fast
  qed
} thus ?thesis by auto
qed


lemma frame_safe_rule:
  assumes a0:"\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c Q,A" and
          a1:"prog_env_safe \<Gamma> c F" and
          a2:"pred_safe \<Gamma> c P"
  shows  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> (P\<and>*\<^sub>sR) c (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
using a0 a1 a2
proof(induct arbitrary: R)
  case (Skip \<Gamma> F Q) thus ?case using hoarep.Skip by fastforce
next
  case (Basic \<Theta> F f Q A) 
    from hoarep.Basic  have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>{s. f s \<in> (Q\<and>*\<^sub>sR)} Basic f (Q\<and>*\<^sub>sR),A" 
      by fastforce
    have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>{s. f s \<in> Q} Basic f Q,A" using  hoarep.Basic by fastforce
    have "\<forall>s. f s \<in> (Q\<and>*\<^sub>sR) \<longrightarrow> (\<exists>s1 s2. (f s) = s1 + s2 \<and> s1 ## s2 \<and> s1\<in>Q  \<and> s2\<in>R)"
      using fun_safe_def
      unfolding  sep_conj_def fun_safe_def by fastforce  
    unfolding prog_env_safe_def prog_safe.simps(2) fun_safe_def
    show " \<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>{a. ((\<lambda>v. v \<in> {s. f s \<in> Q}) \<and>* (\<lambda>v. v \<in> R)) a} Basic f
              {a. ((\<lambda>v. v \<in> Q) \<and>* (\<lambda>v. v \<in> R)) a},
              {a. ((\<lambda>v. v \<in> A) \<and>* (\<lambda>v. v \<in> R)) a}" 
sorry 
next 
  case (Cond \<Theta> F P b c\<^sub>1 Q A c\<^sub>2)    
    then have pred_safe:"(pred_sep_domain b) \<subseteq> (pred_sep_domain P) \<and>  (pred_safe \<Gamma> c\<^sub>1 (P \<inter> b)) \<and> pred_safe \<Gamma> c\<^sub>2 (P \<inter> -b)"
    by (fastforce elim: pred_safe_elim_cases(5))
    then have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>((P \<inter> b) \<and>*\<^sub>s R) c\<^sub>1 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)" using Cond
      unfolding prog_env_safe_def by auto   
    also have "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F \<^esub>((P \<inter> -b) \<and>*\<^sub>s R) c\<^sub>2 (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)" using Cond pred_safe
      unfolding prog_env_safe_def by auto
    ultimately have "\<forall>n. \<Gamma>,\<Theta>\<Turnstile>n:\<^bsub>/F \<^esub>(P \<and>*\<^sub>s R) (Cond b c\<^sub>1 c\<^sub>2) (Q\<and>*\<^sub>sR),(A\<and>*\<^sub>sR)"
      using if_der Cond pred_safe by (metis hoare_cnvalid) 
    then show ?case using hoare_complete' by force
next
 
qed 
  

end