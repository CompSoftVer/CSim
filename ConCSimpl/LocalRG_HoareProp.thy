section \<open>The Proof System\<close>

theory LocalRG_HoareProp imports LocalRG_HoareDef

begin

section \<open>Proof System for Component Programs\<close>

theorem localrgsound:
"\<Gamma>,\<Theta> \<turnstile>\<^bsub>/F\<^esub> c sat [p, I, R, G, q,a] \<Longrightarrow> \<Gamma> \<Turnstile>\<^bsub>/F\<^esub> c sat [pre, i,R, G, q,a]"
sorry
thm case_option_def
end