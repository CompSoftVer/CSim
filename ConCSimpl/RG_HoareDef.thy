theory RG_HoareDef                       
imports "SmallStepCon" "../EmbSimpl/HoarePartialDef"
begin           
section \<open>Validity  of Correctness Formulas\<close>

subsection \<open>Validity for Component Programs.\<close>
type_synonym ('l,'g) state= "('l,'g) action_state"
type_synonym ('l,'g,'p,'f) rgformula =  
   "((('l,'g) state,'p,'f) body \<times>
    'f set \<times>
    (('l,'g) state,'p,'f) com \<times>
    (('l,'g) state \<Rightarrow> bool) \<times>
    (('l,'g) state \<Rightarrow> bool) \<times> 
    (('l,'g) transition \<Rightarrow> bool) \<times>
    (('l,'g) transition \<Rightarrow> bool) \<times> 
    (('l,'g) state \<Rightarrow> bool) \<times>
    (('l,'g) state \<Rightarrow> bool))"

definition assum :: 
  "((('l::sep_algebra,'g::sep_algebra) state \<Rightarrow> bool) \<times>  
   (('l,'g) transition \<Rightarrow> bool) ) \<Rightarrow>
   'f set \<Rightarrow>
     ((('l,'g) state,'p,'f) confs) set" where
  "assum \<equiv> \<lambda>(pre, rely) F. 
             {c. snd((snd c)!0) \<in> Normal ` (Collect pre) \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
                 (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow> 
                 snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow>
                   (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                     (split (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))}"
                                                                                                                                                
definition comm :: 
  "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool)  \<times> 
   ((('l,'g) state \<Rightarrow> bool)\<times> (('l,'g) state \<Rightarrow> bool)) \<Rightarrow>
   'f set \<Rightarrow> 
     ((('l,'g) state,'p,'f) confs) set" where
  "comm \<equiv> \<lambda>(guar, (q,a)) F. 
            {c. (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
               (fst c)\<turnstile>\<^sub>c((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow> 
               snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow>
                 (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
                   (split (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (guar ** tran_True) \<rfloor>)) \<and> 
                 (final_valid (last (snd c)) \<longrightarrow> ((fst (last (snd c)) = Skip \<and> 
                                                  snd (last (snd c)) \<in> Normal ` (Collect q))) \<or>
                                                  (fst (last (snd c)) = Throw \<and> 
                                                  snd (last (snd c)) \<in> Normal ` (the_set a)))}"

definition com_validity :: 
  "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
    'f set \<Rightarrow>
    (('l,'g) state,'p,'f) com \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow>     
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) transition \<Rightarrow> bool) \<Rightarrow>  
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
    (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
      bool" 
    ("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ sat [_,_, _, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Pr sat [p, i , R, G, q,a] \<equiv> 
   \<forall>s. cp \<Gamma> Pr s \<inter> assum(p, R) F \<subseteq> comm(G, (q,a)) F"

subsection \<open>Validity for Parallel Programs.\<close>
definition All_End :: "('s,'p,'f) par_config \<Rightarrow> bool" where
  "All_End xs \<equiv> \<forall>c\<in>set (fst xs). final_valid (c,snd xs)"

definition par_assum :: 
  "((('l::sep_algebra,'g::sep_algebra) state \<Rightarrow> bool) \<times>  
   (('l,'g) transition \<Rightarrow> bool) ) \<Rightarrow>
   'f set \<Rightarrow>
     ((('l,'g) state,'p,'f) par_confs) set" where
  "par_assum \<equiv> 
     \<lambda>(pre, rely) F. {c. 
       snd((snd c)!0) \<in> Normal ` (Collect pre) \<and> (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
       (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow>\<^sub>e ((snd c)!(Suc i)) \<longrightarrow> 
       snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow>
         (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
           (split (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (rely ** tran_Id) \<rfloor>))}"

definition par_comm :: 
  "(('l::sep_algebra,'g::sep_algebra) transition \<Rightarrow> bool)  \<times> 
     ((('l,'g) state \<Rightarrow> bool)\<times> (('l,'g) state \<Rightarrow> bool))  \<Rightarrow> 
    'f set \<Rightarrow>
   ((('l,'g) state,'p,'f) par_confs) set" where
  "par_comm \<equiv> 
     \<lambda>(guar, (q,a)) F. {c. 
       (\<forall>i. Suc i<length (snd c) \<longrightarrow> 
           (fst c)\<turnstile>\<^sub>p((snd c)!i)  \<rightarrow> ((snd c)!(Suc i)) \<longrightarrow> 
           snd ((snd c)!(Suc i)) \<notin> Fault ` F  \<longrightarrow>
           (snd((snd c)!i), snd((snd c)!(Suc i))) \<in> 
             (split (\<lambda>x y. (Normal x, Normal y))) ` (\<lfloor> (guar ** tran_True) \<rfloor>)) \<and> 
           (All_End (last (snd c)) \<longrightarrow> (\<exists>j. fst (last (snd c))!j=Throw \<and> 
                                              snd (last (snd c)) \<in> Normal ` (Collect a)) \<or>
                                       (\<forall>j. fst (last (snd c))!j=Skip \<and>
                                              snd (last (snd c)) \<in> Normal ` (Collect q)))}"

definition par_com_validity :: 
  "(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body \<Rightarrow> 
   'f set \<Rightarrow>
   (('l,'g) state,'p,'f) par_com \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) transition \<Rightarrow> bool) \<Rightarrow> 
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow>
   (('l,'g) state \<Rightarrow> bool) \<Rightarrow> 
     bool"  
("_ \<Turnstile>\<^bsub>'/_\<^esub>/ _ SAT [_, _,_, _, _,_]" [61,60,0,0,0,0,0,0,0] 45) where
  "\<Gamma> \<Turnstile>\<^bsub>/F\<^esub> Ps SAT [pre, i,R, G, q,a] \<equiv> 
   \<forall>s. par_cp \<Gamma> Ps s \<inter> par_assum(pre, R) F \<subseteq> par_comm(G, (q,a)) F"

declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

inductive
lrghoare :: "[(('l::cancellative_sep_algebra,'g::cancellative_sep_algebra) state,'p,'f) body, 
              'f set,
              (('l,'g) state,'p,'f) com,  
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) transition \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool),
              (('l,'g) state \<Rightarrow> bool),
               (('l,'g) state \<Rightarrow> bool)] \<Rightarrow> bool"
    ("_ \<turnstile>\<^bsub>'/_\<^esub> _ sat [_, _, _, _, _,_]" [61,60,60,0,0,0,0,0] 45)
where
 Skip: "\<lbrakk> Sta q (R\<and>*tran_Id); 
          Sta a (R\<and>*tran_Id); 
          I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow>
         \<Gamma> \<turnstile>\<^bsub>/F\<^esub> Skip sat [q, I, R, G, q,a] "

|Spec: "\<lbrakk>Collect p \<subseteq> {s. (\<forall>t. (s,t)\<in>r \<longrightarrow> t \<in> Collect q) \<and> (\<exists>t. (s,t) \<in> r)};
        \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
        \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t);
        Sta p (R\<and>*tran_Id); Sta q (R\<and>*tran_Id); 
        Sta a (R\<and>*tran_Id); 
        I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Spec r) sat [p, I, R, G, q,a]"

| Basic: "\<lbrakk> Collect p \<subseteq> {s. f s \<in> (Collect q)}; 
           \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
           \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t);
           Sta p (R\<and>*tran_Id); Sta q (R\<and>*tran_Id); Sta a (R\<and>*tran_Id); I  \<triangleright> R; I  \<triangleright> G \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Basic f) sat [p, I, R, G, q,a]"

| If: "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p and (set_fun b), I, R, G, q,a]; 
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c2 sat [p and (not (set_fun b)), I, R, G, q,a]\<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Cond b c1 c2) sat [p, I, R, G, r,a]"

| While: "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun b), I, R, G, p,a] \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (While b c) sat [p, I, R, G, q and (not (set_fun b)),a]"

| Seq: "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,a]; \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c2 sat [q, I, R, G, r,a]\<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Seq c1 c2) sat [p, I, R, G, r,a]"

| Await: "\<lbrakk> \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p \<inter> b) c (Collect q),(Collect A);
           \<forall>s t. ((p or (q or a)) imp (I\<and>*sep_true)) (s,t);
           \<forall>s t. ((p \<unrhd> q) imp (G\<and>*tran_True)) (s,t);
           Sta p (R\<and>*tran_Id); Sta q (R\<and>*tran_Id); Sta a (R\<and>*tran_Id); I  \<triangleright> R; I  \<triangleright> G \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Await b c) sat [p, I, R, G, q,a]"

| Guard: "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun g), I, R, G, p,a] \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p and (set_fun g), I, R, G, q,a]"

| Guarantee:  "\<lbrakk> f\<in>F; \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c sat [p and (set_fun g), I, R, G, p,a] \<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Guard f g c) sat [p, I, R, G, q,a]"

| CallRec: "\<lbrakk>c \<in> dom \<Gamma>; \<Gamma>\<turnstile>\<^bsub>/F\<^esub> (the (\<Gamma> c)) sat [p, I, R, G, q,a]\<rbrakk> \<Longrightarrow>
            \<Gamma>\<turnstile>\<^bsub>/F\<^esub> (Call c) sat [p, I, R, G, q,a]"

| DynCom: "\<lbrakk>\<forall>s \<in> Collect p. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> (c s) sat [p, I, R, G, q,a]\<rbrakk> \<Longrightarrow>
            \<Gamma>\<turnstile>\<^bsub>/F\<^esub> (DynCom c) sat [p, I, R, G, q,a]"

| Throw: "\<lbrakk> Sta q (R\<and>*tran_Id); 
          Sta a (R\<and>*tran_Id); 
          I  \<triangleright> R; I  \<triangleright> G\<rbrakk> \<Longrightarrow>
         \<Gamma> \<turnstile>\<^bsub>/F\<^esub> Throw sat [a, I, R, G, q,a] "

| Catch: "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c1 sat [p, I, R, G, q,r]; \<Gamma> \<turnstile>\<^bsub>/F\<^esub> c2 sat [r, I, R, G, r,a]\<rbrakk> \<Longrightarrow>
        \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (Catch c1 c2) sat [p, I, R, G, r,a]"

| Conseq: "\<lbrakk> \<forall>s \<in> (Collect p). 
             (\<exists>p' R' G' q' a' I'.  (p' s) \<and>
             (\<forall>s t. (R  imp R') (s,t)) \<and>            
             (\<forall>s t. (G' imp G) (s,t)) \<and>             
             (\<forall>s. (q' imp q) s) \<and>
             (\<forall>s. (a' imp a) s) \<and>
             (\<forall>s t. ((p' or (q' or a')) imp (I'\<and>*sep_true)) (s,t)) \<and>             
            (I'  \<triangleright> R')\<and> (I' \<triangleright> G') \<and>             
            \<Gamma>\<turnstile>\<^bsub>/F\<^esub> P sat [p', I', R', G', q',a'] )\<rbrakk>
            \<Longrightarrow> \<Gamma>\<turnstile>\<^bsub>/F\<^esub> P sat [p, I, R, G, q,a]"

| Env:  "\<lbrakk>noawaits c; \<Gamma>\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (Collect p ) (sequential c) (Collect q),(Collect a)\<rbrakk> \<Longrightarrow>
         \<Gamma>\<turnstile>\<^bsub>/F\<^esub> c sat [p, sep_empty, Emp, Emp, q,a]
        "

definition Pre :: " ('l,'g,'p,'f)rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Pre x \<equiv> fst(snd(snd(snd x)))"

definition Post :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Post x \<equiv>  snd(snd(snd(snd(snd(snd(snd(snd x)))))))"

definition Inva :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Inva x \<equiv> fst(snd(snd(snd(snd x))))"

definition Abr :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state \<Rightarrow> bool)" where
  "Abr x \<equiv> fst(snd(snd(snd(snd(snd(snd(snd x)))))))"

definition Rely :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) transition \<Rightarrow> bool)" where
  "Rely x \<equiv> fst(snd(snd(snd(snd(snd x)))))"

definition Guar :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) transition \<Rightarrow> bool)" where
  "Guar x \<equiv> fst(snd(snd(snd(snd(snd(snd x))))))"

definition Com :: "('l,'g,'p,'f) rgformula \<Rightarrow> (('l,'g) state,'p,'f) com" where
  "Com x \<equiv> fst (snd (snd x))"

inductive
  par_rghoare ::  "[(('l::cancellative_sep_algebra,'g::cancellative_sep_algebra) state,'p,'f) body, 
              'f set,
              ( ('l,'g,'p,'f) rgformula) list,  
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) state \<Rightarrow> bool), 
              (('l,'g) transition \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool),
              (('l,'g) state \<Rightarrow> bool),
               (('l,'g) state \<Rightarrow> bool)] \<Rightarrow> bool"
    ("_ \<turnstile>\<^bsub>'/_\<^esub> _ SAT [_, _, _, _, _,_]" [61,60,60,0,0,0,0,0] 45)
where
  Parallel:
  "\<lbrakk> \<forall>i<length xs. (Collect rely) \<union> (\<Union>j\<in>{j. j<length xs \<and> j\<noteq>i}. (Collect (Guar(xs!j)))) \<subseteq> (Collect (Rely(xs!i)));
    (\<Union>j<length xs. (Collect (Guar(xs!j)))) \<subseteq> (Collect guar);
     (Collect pre) \<subseteq> (\<Inter>i<length xs. (Collect (Pre(xs!i))));
    (\<Inter>i<length xs. (Collect (Post(xs!i)))) \<subseteq> (Collect post);
    (\<Union>i<length xs. (Collect (Abr(xs!i)))) \<subseteq> (Collect abr);
    (pre = (p \<and>* r)) \<and> (\<forall>i<length xs. \<exists>pi. Pre(xs!i) = (pi \<and>* r));
    (post = (q\<and>*rq)) \<and> (\<forall>i<length xs.(\<Inter>{crj.  \<exists>rj qj. Post(xs!i) = (qj\<and>*rj) \<and> crj=Collect rj} \<subseteq> Collect rq));
    (abr = (abr\<and>*rabr)) \<and> (\<forall>i<length xs.(\<Union>{crj.  \<exists>abrj rabrj. Abr(xs!i) = (abrj\<and>*rabrj) \<and> crj=Collect rj} \<subseteq> Collect rabr));
     \<forall>s t.((r or rq or rabr) imp inva)(s,t);
    (* ((Collect r) \<union> (\<Union>{crj. \<forall>i<length xs. \<exists>abrj rabrj. Abr(xs!i) = (abrj\<and>*rabrj) \<and> crj= Collect rj} )) \<subseteq> (Collect inva); *)
    inva  \<triangleright> rely;
    \<forall>i<length xs. \<Gamma>\<turnstile>\<^bsub>/F\<^esub> Com(xs!i) sat [Pre(xs!i),Inva(xs!i),Rely(xs!i),Guar(xs!i),Post(xs!i),Abr(xs!i)] \<rbrakk>
   \<Longrightarrow>  \<Gamma>\<turnstile>\<^bsub>/F\<^esub> xs SAT [pre, inva, rely, guar, post,abr]"


end