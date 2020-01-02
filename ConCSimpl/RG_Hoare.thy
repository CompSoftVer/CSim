section \<open>The Proof System\<close>

theory RG_Hoare imports RG_HoareDef

begin

subsection \<open>Proof System for Component Programs\<close>

declare Un_subset_iff [simp del] sup.bounded_iff [simp del]

inductive
lrghoare :: "[(('l::sep_algebra,'g::sep_algebra) state,'p,'f) body, (('l,'g) state,'p,'f) com,  (('l,'g) state \<Rightarrow> bool), (('l,'g) state \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool), (('l,'g) transition \<Rightarrow> bool),  (('l,'g) state \<Rightarrow> bool)] \<Rightarrow> bool"
    ("_ \<turnstile> _ sat [_, _, _, _, _]" [0,60,0,0,0,0] 45)
where
 Basic: "\<Gamma> \<turnstile> (Basic f) sat [pre, rely, guar, post, inva]"

end