(*
    Author:      David Sanan
    Maintainer:  David Sanan, sanan at ntu edu sg
    License:     LGPL
*)

(*  Title:      ArincMultiCoreServices.thy
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
theory ArincSpec_com_queue_insert
imports "ArincQueuing" 
begin 
  
section {* tests *}
  
(*declare[[ML_print_depth = 50000]]*)
(* setup{*
  Config.put_global Proof_Context.debug true *}
ML\<open>
local 
fun sleep b m t = Method.RUNTIME (fn ctxt_st =>
let val _ = writeln (m ^ (if b then " " ^ (@{make_string} ((#1 ctxt_st) |> Proof_Display.pp_context )) else "")) in
 (OS.Process.sleep t; Seq.single (Seq.Result ctxt_st)) end)
in
fun g b m = 
Method.NO_CONTEXT_TACTIC @{context} (sleep b m (Time.fromSeconds 0))
end

\<close>
  
ML{*
val _ = CONTEXT_METHOD
val _ = METHOD
val _ = Seq.succeed
val _ = Theory.setup
 ( Method.setup @{binding succeed2} (Scan.succeed (fn ctxt => 
K (CONTEXT_METHOD (fn using => fn ccc => Method.RUNTIME (fn (goal_ctxt, st) =>
let val _ = writeln ("qqqq" ^ @{make_string} (using, ccc)) in
 (goal_ctxt, st) |> Seq.Result |>   Seq.succeed end) ccc)) ctxt)) "succeed")*}
   *) 
section {* Event Specification *}

  
  

subsection {* send queuing message param *}

definition send_q_message_i::"nat \<Rightarrow> (vars,(Evnt\<times>nat),Faults,Events) com"
where
"send_q_message_i i \<equiv>
   IF (\<not> (p_queuing conf \<acute>communication (pt (\<acute>locals!i)))) \<or>  
       (\<not> (p_source conf \<acute>communication (pt (\<acute>locals!i)))) \<or>
       (\<not> port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals!i))) (pt (\<acute>locals!i))) \<or> 
       ( \<not> port_open \<acute>communication (pt (\<acute>locals!i))) \<or>
       ( \<not> (snd (msg (\<acute>locals!i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals!i))))   
    THEN
        \<acute>locals :==\<^sub>E\<^sub>V \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 0\<rparr>)]
   ELSE       
     (AWAIT\<^sub>\<down>\<^sub>E\<^sub>V (port_get_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) = 0)
        (\<acute>communication :==\<^sub>s (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) (i+1))));;
     AWAIT\<^sub>\<down>\<^sub>E\<^sub>V True 
     (IF\<^sub>s port_full conf \<acute>communication (pt ((\<acute>locals)!i))  THEN          
       (\<acute>locals :==\<^sub>s \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 1\<rparr>)];;\<^sub>s
       \<acute>communication :==\<^sub>s (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) 0))
     ELSE
       (\<acute>communication :==\<^sub>s 
          port_insert_message conf \<acute>communication
            (pt (\<acute>locals!i)) (msg (\<acute>locals!i)) 0  ;;\<^sub>s
       \<acute>locals :==\<^sub>s 
          \<acute>locals[i:=((\<acute>locals!i)
             \<lparr>a_que_aux := set_que_aux conf \<acute>communication (pt ((\<acute>locals)!i)) (a_que_aux (\<acute>locals ! i)) 
                            (get_que_aux conf \<acute>communication (pt ((\<acute>locals)!i)) (a_que_aux (\<acute>locals ! i)) + 
                              {# (msg (\<acute>locals!i)) #})
             \<rparr>)];;\<^sub>s                  
       \<acute>communication :==\<^sub>s (port_set_mutex conf \<acute>communication (pt ((\<acute>locals)!i)) 0);;\<^sub>s
       \<acute>locals :==\<^sub>s \<acute>locals[i:=((\<acute>locals!i)\<lparr>ret_n := 1\<rparr>)])        
     FI)
   FI                  
"


subsection {* receive queuing message param *}



(* remove for Case-Study 
lemma body_receive: "i<n  \<Longrightarrow> \<Gamma> (Receive_Message_Q,i) = Some (receive_q_message_i i)"
unfolding \<Gamma>_def by auto

lemma body_clear: "i<n \<Longrightarrow> \<Gamma> (Clear_Message_Q,i) = Some (clear_q_message_i i)"
unfolding \<Gamma>_def by auto
*)




subsection {* instructions preserving locals  *}

lemma ret_chan_preserves_locals:
  "i< length (locals_' x) \<Longrightarrow>
   x' =  x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := m\<rparr>]\<rparr> \<Longrightarrow>
   (x,x',i) \<in> preserves_locals_constr \<and>
   a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i) \<and>
   r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i) \<and>
   chans (communication_' x) = chans(communication_' x') \<and>
   ports (communication_' x) = ports(communication_' x')"
 unfolding preserves_locals_constr_def by auto

lemma modify_mutex_preserves_locals: 
  "state_conf s \<Longrightarrow>
   port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
   port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ch_id \<Longrightarrow>       
   s' = s\<lparr>communication_' := 
          port_set_mutex conf (communication_' s) (pt (locals_' s ! i)) m\<rparr> \<Longrightarrow>     
     (s,s', i) \<in> preserves_locals_constr \<and>
     (s,s',ch_id) \<in> preserves_comm_constr \<and>
     channel_get_messages (the (chans (communication_' s) ch_id)) = 
     channel_get_messages (the (chans (communication_' s') ch_id)) \<and> 
     channel_get_mutex (the (chans (communication_' s') ch_id)) = m \<and>
     a_que_aux ((locals_' s)!i) = a_que_aux ((locals_' s')!i) \<and>
     r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' s')!i)"        
   apply (frule port_channel, assumption+)
  unfolding    preserves_comm_constr_def port_set_mutex_def 
               preserves_locals_constr_def channel_set_mutex_def channel_get_messages_def
              channel_get_mutex_def  
  by auto
    
 lemma modify_mutex_ret_preserves_locals: 
  " i<length (locals_' s) \<Longrightarrow> 
    state_conf s \<Longrightarrow>
    port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
    port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ch_id \<Longrightarrow>       
   s' = s\<lparr>locals_' := (locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := m\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' s) (pt ((locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := m\<rparr>] ! i)) v\<rparr> \<Longrightarrow>     
     (s,s', i) \<in> preserves_locals_constr \<and>
     (s,s',ch_id) \<in> preserves_comm_constr \<and>
     channel_get_messages (the (chans (communication_' s) ch_id)) = 
     channel_get_messages (the (chans (communication_' s') ch_id)) \<and> 
     channel_get_mutex (the (chans (communication_' s') ch_id)) = v \<and>
     a_que_aux ((locals_' s)!i) = a_que_aux ((locals_' s')!i) \<and>
     r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' s')!i)"      
   apply (frule port_channel, assumption+)
  unfolding  Invariant_def  preserves_comm_constr_def port_set_mutex_def 
              Let_def preserves_locals_constr_def  
              port_in_channel_def port_channel_def channel_set_mutex_def channel_get_messages_def
              channel_get_mutex_def port_name_in_channel_def port_id_name_def
   by auto   

 lemma transit_send_que_preserve_locals:
  "i< length (locals_' s) \<Longrightarrow>
  state_conf  s \<Longrightarrow>
  port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
  port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ch_id \<Longrightarrow>
  p_queuing conf  (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
   port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i \<Longrightarrow>
   s' = s\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) t)
               (pt (locals_' s !i)) 0,
             locals_' := (locals_' s) [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr> \<Longrightarrow>
   (s,s',i) \<in> preserves_locals_constr \<and> 
   (s,s', ch_id) \<in> preserves_comm_constr \<and>    
    msg ((locals_' s)!i) = msg ((locals_' s')!i) \<and> 
    a_que_aux ((locals_' s')!i) ch_id = a_que_aux ((locals_' s)!i) ch_id + ({# (msg (locals_' s ! i)) #}) \<and>
    (\<forall>j. j\<noteq>ch_id \<longrightarrow> a_que_aux ((locals_' s')!i) j = a_que_aux ((locals_' s)!i) j) \<and>
    r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' s')!i)  \<and>
    channel_get_mutex (the (chans (communication_' s) ch_id))  \<noteq> 0 \<and>    
    channel_get_mutex (the (chans (communication_' s') ch_id)) = 0 \<and>
     channel_get_messages (the (chans (communication_' s) ch_id)) + 
             {# msg ((locals_' s')!i) #} =  
          channel_get_messages (the (chans (communication_' s') ch_id))"   
   apply (frule port_channel, assumption+)
     apply (frule p_queuing_chan_queuing,assumption+)     
   unfolding    preserves_comm_constr_def port_set_mutex_def 
               preserves_locals_constr_def  port_get_mutex_def
               port_insert_message_def port_exists_def
             channel_get_mutex_def chan_queuing_def chan_sampling_def channel_insert_message_def
             channel_set_messages_def channel_get_messages_def port_set_mutex_def set_que_aux_def get_que_aux_def
             channel_set_mutex_def  Let_def port_channel_def port_in_channel_def port_name_in_channel_def port_id_name_def             
  by(cases "data (the (chans (communication_' s) ch_id))",auto)
    
  lemma transit_send_que_preserve_locals':
  "i< length (locals_' s) \<Longrightarrow>
  state_conf  s \<Longrightarrow>
  port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
  port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ch_id \<Longrightarrow>
   s' = s\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) t)
               (pt (locals_' s !i)) 0,
             locals_' := (locals_' s) [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr> \<Longrightarrow>
   (s,s',i) \<in> preserves_locals_constr \<and> 
   (s,s', ch_id) \<in> preserves_comm_constr \<and>            
    (\<forall>j. j\<noteq>ch_id \<longrightarrow> a_que_aux ((locals_' s')!i) j = a_que_aux ((locals_' s)!i) j) \<and>
    r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' s')!i)"
  apply (frule port_channel, assumption+)
  unfolding   preserves_comm_constr_def  port_exists_def
              Let_def preserves_locals_constr_def  
              port_insert_message_def port_set_mutex_def set_que_aux_def 
              port_channel_def port_in_channel_def  port_id_name_def
 by auto



subsection {* instructions preserving Invariant  *}

lemma modify_mut_chan:
  "state_conf  x \<Longrightarrow>
   i<length (locals_' x) \<Longrightarrow>
   port_open (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
   channel_spec B adds rems ch_id x \<Longrightarrow>    
   port_in_channel conf  (communication_' x) (pt (locals_' x ! i)) ch_id \<Longrightarrow>    
   x' = 
   x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) m\<rparr> \<Longrightarrow>
   channel_spec B adds rems ch_id x'"
  apply (frule modify_mutex_preserves_locals,auto)
  apply (rule local_constr_ch_spec_channel_spec)
  using p_chan by auto

lemma modify_ret_inv:"i< procs conf \<Longrightarrow> 
      x\<in> Invariant B adds rems i \<Longrightarrow> 
      x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := m\<rparr>]\<rparr> \<in> Invariant B adds rems i"
proof-
  assume a0:"i< procs conf" and
         a1:"x\<in> Invariant B adds rems i"
   then have a0:"i<length (locals_' x)" unfolding Invariant_def state_conf_def by auto
  thus ?thesis
    using Invariant_eq ret_chan_preserves_locals a1    
    by blast
qed  
 
lemma modify_mut_inv':
   "i< length (locals_' x) \<Longrightarrow> 
   port_open (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
   x\<in> Invariant B adds rems i \<Longrightarrow> 
   x' = x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) m\<rparr> \<Longrightarrow>  
   channel_spec B adds rems (port_channel conf (communication_' x) (pt (locals_' x !i))) x'"
  unfolding Invariant_def          
  apply auto
  using  modify_mut_chan port_unique_channel by metis
  
lemma modify_mut_inv'':
   "x\<in>  Invariant B adds rems i\<Longrightarrow> 
   x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) m\<rparr> \<in>
      {s. state_conf  s}
   "             
  unfolding Invariant_def state_conf_def Let_def  port_set_mutex_def 
  chan_queuing_def chan_sampling_def channel_set_mutex_def  port_exists_def
  by auto
 

lemma modify_mut_inv:
   "i< procs conf \<Longrightarrow> 
    port_open (communication_' x) (pt (locals_' x ! i))  \<Longrightarrow>
   x\<in> Invariant B adds rems i \<Longrightarrow> 
   x' = x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) m\<rparr> \<Longrightarrow>
   x' \<in> Invariant B adds rems i"
  apply (drule procs_len_locals,assumption)   
  apply (frule modify_mut_inv'[of _ _ _ _ _ _ m], simp+)
  apply (frule modify_mut_inv''[of _ _ _ _ _ m], simp+)       
  apply (subgoal_tac "ports (communication_' x) = ports (communication_' x')")
    apply (drule port_channl_eq_pid[of _ _ "(pt (locals_' x ! i))"], simp) 
  unfolding Invariant_def 
   apply auto
   by (auto simp add: port_set_mutex_def channel_set_mutex_def Let_def)
  
    
     
 (* by (cases "data (the (chans (communication_' s) ch_id))",auto)   *)

lemma modify_mut_zero_ret_chan:
   "state_conf  s \<Longrightarrow>
   i<length (locals_' s) \<Longrightarrow>
   channel_spec B adds rems ch_id s \<Longrightarrow> 
   port_open (communication_' s) (pt (locals_' s !i)) \<Longrightarrow> 
   port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ch_id \<Longrightarrow>
   s' = s\<lparr>locals_' := (locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := m\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' s) (pt (locals_' s ! i)) v\<rparr> \<Longrightarrow>
    channel_spec B adds rems ch_id s'"  
   apply (frule modify_mutex_ret_preserves_locals,auto)
  apply (rule local_constr_ch_spec_channel_spec)
  using p_chan by auto
    
lemma modify_mut_zero_ret_inv':
assumes a0:"i < length (locals_' x)" and
   a1:"x \<in> Invariant B adds rems i" and
  a2:"port_open (communication_' x) (pt (locals_' x !i))" and
  a3:"x' = x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt ((locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>" 
shows "channel_spec B adds rems (port_channel conf  (communication_' x')(pt (locals_' x' !i))) x'"  
proof -
  have a1:"state_conf x" and 
     a1':"channel_spec B adds rems (port_channel conf  (communication_' x)(pt (locals_' x !i))) x"
    using a1 unfolding Invariant_def by auto
  have "channel_spec B adds rems (port_channel conf  (communication_' x)(pt (locals_' x !i))) x'"
    using a3 a0 apply auto 
   using port_exist_unique_channel[OF a1 a2] 
    modify_mut_zero_ret_chan[OF a1 a0 a1' a2] port_channel[OF a1 a2]
   by blast 
  moreover have "port_channel conf  (communication_' x')(pt (locals_' x' !i)) = 
                 port_channel conf  (communication_' x)(pt (locals_' x !i))"  
   using  modify_mutex_ret_preserves_locals[OF a0 a1 a2 _ a3]
   using a1 a2  preserves_locals_D3  exist_port_in_channel preserves_comm_D3
   by (metis port_channl_eq_ports)   
  ultimately show ?thesis
    by simp 
qed          


lemma modify_mut_ret_inv'':
   " i< length (locals_' x) \<Longrightarrow>
   port_open (communication_' x) (pt (locals_' x !i)) \<Longrightarrow>
   x\<in>  Invariant B adds rems i \<Longrightarrow> 
  x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt ((locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr> \<in>
      {s. state_conf s}
   "
  using port_exist_unique_channel port_channel
  unfolding Invariant_def state_conf_def
            Let_def  port_set_mutex_def 
         chan_queuing_def chan_sampling_def channel_set_mutex_def port_exists_def
  by auto
 
(* lemma modify_mut_ret_inv''':
assumes  a0: " i< length (locals_' x)" and
   a1:"port_open (communication_' x) (pt (locals_' x !i))" and
  a2:"x\<in>  Invariant B adds rems i" 
  shows "x\<lparr>locals_' := locals_' x[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt (locals_' x[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr> \<in>
      \<lbrace>channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) r_que_aux \<acute>locals \<and>
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) a_que_aux \<acute>locals\<rbrace>
   "
proof-
  let ?x' = "x\<lparr>locals_' := locals_' x[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt (locals_' x[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>"
  let ?p = "(port_channel conf (communication_' x) (pt (locals_' x ! i)))"
  have "port_in_channel conf (communication_' x) (pt (locals_' x ! i)) ?p"
    using port_exist_unique_channel port_channel a2 a1 unfolding Invariant_def by fastforce
  then have prev:"(x,?x', i) \<in> preserves_locals_constr \<and>
     (x,?x',?p) \<in> preserves_comm_constr \<and>
     channel_get_messages (the (chans (communication_' x) ?p)) = 
     channel_get_messages (the (chans (communication_' ?x') ?p)) \<and> 
     a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' ?x')!i) \<and>
     r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' ?x')!i)"  
    using modify_mutex_ret_preserves_locals[OF a0 _ a1 ] a2[simplified Invariant_def] by auto
  then have "?x'\<in> \<lbrace>channel_messages ?p rems [0..<length (locals_' ?x')] \<subseteq>#
        channel_messages ?p r_que_aux (locals_' ?x') \<and>
        channel_messages ?p adds [0..<length (locals_' ?x')] \<subseteq>#
        channel_messages ?p a_que_aux (locals_' ?x')\<rbrace>"
    using local_constr_subset_aux 
    IntE Invariant_def a2 mem_Collect_eq 
    by (metis (no_types, lifting) IntE Invariant_def a2 mem_Collect_eq)
  moreover have "?p = port_channel conf (communication_' ?x') (pt (locals_' ?x' ! i))"
    using prev port_channl_eq_pid   preserves_comm_D3 preserves_locals_D3
    by (metis (no_types, lifting))         
  ultimately show ?thesis by force
qed   *)
           
lemma modify_mut_zero_ret_inv:
   "i<procs conf \<Longrightarrow>
   x \<in> Invariant B adds rems i\<Longrightarrow>
   port_open (communication_' x) (pt (locals_' x !i))    \<Longrightarrow>        
   x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt ((locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>
       \<in> Invariant B adds rems i"
  apply (drule procs_len_locals,assumption)    
using modify_mut_zero_ret_inv' modify_mut_ret_inv''
  unfolding Invariant_def by fast
  
  

lemma modify_ret_n_guarantee: "i < procs conf \<Longrightarrow>
       state_conf s \<Longrightarrow> 
       (Normal s, Normal (s\<lparr>locals_' := (locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := u\<rparr>]\<rparr>))
       \<in> Guarantee_Send_Receive i "
  unfolding Guarantee_Send_Receive_def Guarantee_Send_Receive'_def state_conf_def    
     Guarantee_mod_chan_def Let_def port_exists_def
  by auto

    
lemma modify_mutex_send_guarantee: 
   "i < procs conf \<Longrightarrow> state_conf s  \<Longrightarrow>   
   p_queuing conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
   port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = 0 \<Longrightarrow>   
   (Normal s, Normal (s\<lparr>communication_' := 
          port_set_mutex conf (communication_' s) (pt (locals_' s ! i)) (Suc i)\<rparr>))
      \<in> Guarantee_Send_Receive i "
unfolding state_conf_def Invariant_def Guarantee_Send_Receive'_def Guarantee_Send_Receive_def  port_set_mutex_def 
                port_get_mutex_def channel_get_mutex_def chan_queuing_def channel_get_messages_def
              channel_set_mutex_def ch_id_queuing_def Let_def p_queuing_def chan_sampling_def
            Guarantee_mod_chan_def  Let_def port_exists_def    
  by auto
  


(* lemmas For the atomic version *)
lemma modify_ret_mutex_zero_guarantee:
 " i < procs conf \<Longrightarrow>
   state_conf s   \<Longrightarrow>           
   port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i \<Longrightarrow>                  
   p_queuing conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
   (Normal s,
    Normal (s\<lparr>locals_' := (locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := Suc 0\<rparr>],
                communication_' :=
                  port_set_mutex conf (communication_' s)
                   (pt ((locals_' s)[i := (locals_' s ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>))
   \<in> Guarantee_Send_Receive i"
   unfolding state_conf_def Guarantee_Send_Receive'_def Guarantee_Send_Receive_def  port_set_mutex_def 
                port_get_mutex_def channel_get_mutex_def chan_queuing_def channel_get_messages_def
              channel_set_mutex_def ch_id_queuing_def Let_def p_queuing_def chan_sampling_def
            Guarantee_mod_chan_def port_exists_def  
 by auto  
         
lemma insert_queue_preserves_ch_spec:
assumes a0:"i < length (locals_' s)" and
        a1:"s \<in> Invariant B adds rems i" and        
        a3:"port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i" and
        a4:"evnt (locals_' s ! i) = ev" and
        a5:"p_source conf (communication_' s) (pt (locals_' s ! i))" and
        a6:"p_queuing conf (communication_' s) (pt (locals_' s ! i))" and
        a7:"port_open (communication_' s) (pt (locals_' s ! i))" and        
        a9:"\<not> port_full conf (communication_' s) (pt (locals_' s ! i))" and
        a10:"t=s\<lparr>communication_' :=
            port_set_mutex conf
             (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) ti)
             (pt ((locals_' s)
                   [i := (locals_' s ! i)
                    \<lparr>a_que_aux :=
                      set_que_aux conf  (communication_' s)  (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                      (add_mset (msg (locals_' s ! i))
                        (get_que_aux conf  (communication_' s)  (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !i)) 0,
           locals_' := (locals_' s) [i := ((locals_' s)
                           [i := (locals_' s ! i)
                         \<lparr>a_que_aux := set_que_aux  conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                           (add_mset (msg (locals_' s ! i))
                           (get_que_aux conf  (communication_' s)  (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] ! i) \<lparr>ret_n := Suc 0\<rparr>]\<rparr>" 
 shows "channel_spec B adds rems (port_channel conf (communication_' t) (pt (locals_' t !i))) t"  
proof-  
  have a10':
      "t=s\<lparr>communication_' := 
             port_set_mutex conf 
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) ti)
               (pt (locals_' s !i)) 0,
             locals_' := (locals_' s) [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"    
    using a10 a0 by auto
  then have pt:"pt (locals_' s ! i) = pt (locals_' t ! i)" 
    using a0 by auto
  let ?ch = "port_channel conf (communication_' s) (pt (locals_' s!i))"
  have port_in_channel:
   "port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ?ch "
     using a0 a1  a7 port_exist_unique_channel port_channel 
     unfolding Invariant_def  by fast
  then obtain chan where chan:"chans (communication_' s) ?ch = Some chan"
    using a0 a1   
    unfolding Invariant_def state_conf_def port_in_channel_def port_name_in_channel_def
    by fastforce
  then obtain chan' where chan':"chans (communication_' t) ?ch = Some chan'"
      using a0 a1  a3 a4 a5 a6  a9 a10' a7
      unfolding Invariant_def state_conf_def   
                 port_insert_message_def Let_def 
                 port_set_mutex_def
      by fastforce
   have state:
     "state_conf s" using a0 a1 unfolding Invariant_def by auto   
   have 
     channel_spec:"channel_spec B adds rems ?ch s"  and
     a0':"(s,t,i) \<in> preserves_locals_constr" and 
      a1:"(s,t, ?ch) \<in> preserves_comm_constr" and      
     a3:"msg ((locals_' s)!i) = msg ((locals_' t)!i)" and
     a4:"a_que_aux ((locals_' t)!i) ?ch = a_que_aux ((locals_' s)!i) ?ch + ({# (msg (locals_' s ! i)) #}) \<and> 
         (\<forall>j. j\<noteq>?ch \<longrightarrow> a_que_aux ((locals_' t)!i) j = a_que_aux ((locals_' s)!i) j) \<and>
         r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' t)!i)" and
     qmut_not_zero: "channel_get_mutex (the (chans (communication_' s) ?ch)) \<noteq> 0" and
     eq_qmut : "channel_get_mutex (the (chans (communication_' t) ?ch)) = 0" and     
     a6: "i< length (locals_' s)" and 
     a7': "p_queuing conf (communication_' s) (pt (locals_' s !i))" and
     a8: "\<not> port_full conf (communication_' s) (pt(locals_' s!i))" and
     a9: "channel_get_messages chan + {# msg ((locals_' s)!i) #} =  
            channel_get_messages chan'" and
     a10:"channel_get_messages (the (chans (communication_' s) ?ch)) + {# msg ((locals_' s)!i) #} =  
            channel_get_messages (the (chans (communication_' t) ?ch))" 
     using a0 a1  a3 a4 a5 a6  a9 a10' chan chan' 
           transit_send_que_preserve_locals [OF a0 state a7 port_in_channel _ _ a10']  state  
     unfolding Invariant_def by auto
     also have a5:"ch_spec B adds rems ?ch s" 
       using channel_spec_dest2[OF channel_spec] a7'[simplified p_queuing_def]
       using chan by auto
     then have "ch_spec B adds rems ?ch t"  
       using  atomic_tran_channel_ch_spec[OF a0 state a0' a10 _ _ a1 port_in_channel a7 a7' a5 a8]
         a4  
       unfolding ch_spec_def channel_received_messages_def channel_sent_messages_def by fastforce
     moreover have "port_channel conf (communication_' t) (pt (locals_' s!i)) = ?ch"
       by (metis (no_types) a1 port_channl_eq_ports preserves_comm_D3)            
     ultimately show ?thesis
       by (simp add: channel_spec_intro pt)            
   qed
     
(* lemma insert_queue_preserves_aux_subset1:
assumes a0:"i < length (locals_' s)" and
        a1:"s \<in> Invariant B adds rems i" and        
        a3:"port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i" and         
        a6:"p_queuing conf (communication_' s) (pt (locals_' s ! i))" and
        a7:"port_open (communication_' s) (pt (locals_' s ! i))" and
        a10:"t=s\<lparr>communication_' :=
            port_set_mutex conf
             (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) ti)
             (pt (locals_' s
                   [i := (locals_' s ! i)
                    \<lparr>a_que_aux :=
                      set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                      (add_mset (msg (locals_' s ! i))
                        (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !i)) 0,
           locals_' := locals_' s [i := (locals_' s
                           [i := (locals_' s ! i)
                         \<lparr>a_que_aux := set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                           (add_mset (msg (locals_' s ! i))
                           (get_que_aux conf  (communication_' s) (pt (locals_' s ! i))  (a_que_aux (locals_' s ! i))))\<rparr>] ! i) \<lparr>ret_n := Suc 0\<rparr>]\<rparr>" 
 shows "channel_messages (port_channel conf (communication_' s) (pt (locals_' s !i))) rems [0..<length (locals_' t)] \<subseteq># 
          channel_messages  (port_channel conf (communication_' s) (pt (locals_' s !i))) r_que_aux (locals_' t)"  
proof-  
  have a10':
      "t=s\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) ti)
               (pt (locals_' s !i)) 0,
             locals_' := locals_' s [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"    
    using a10 a0 by auto
  then have pt:"pt (locals_' s ! i) = pt (locals_' t ! i)" 
    using a0 by automodify_mut_ret_inv'''
  let ?ch = "port_channel conf (communication_' s) (pt (locals_' s!i))"
  have port_in_channel:
   "port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ?ch "
     using a0 a1 a7  port_exist_unique_channel port_channel 
     unfolding Invariant_def  by fast  
   have state:
     "state_conf s" using a0 a1 unfolding Invariant_def by auto   
   have r_aux_sub:" channel_messages ?ch rems [0..<length (locals_' s)] \<subseteq>#
          channel_messages ?ch r_que_aux (locals_' s)"
     using a1 unfolding Invariant_def channel_spec_def by auto
   have 
     channel_spec:"channel_spec B adds rems ?ch s"  and
     a0':"(s,t,i) \<in> preserves_locals_constr" and       
     a4:"a_que_aux ((locals_' t)!i) ?ch = a_que_aux ((locals_' s)!i) ?ch + ({# (msg (locals_' s ! i)) #}) \<and> 
         (\<forall>j. j\<noteq>?ch \<longrightarrow> a_que_aux ((locals_' t)!i) j = a_que_aux ((locals_' s)!i) j) \<and>
         r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' t)!i)"  
     using  a1  a3  a6   
           transit_send_que_preserve_locals [OF a0 state a7 port_in_channel _ _ a10']    
     unfolding Invariant_def by auto
    show ?thesis
      using a0' a4 add_channel_message_not_evnt preserves_locals_D1 pt r_aux_sub by fastforce
  qed     *)
    
(* lemma insert_queue_preserves_aux_subset2:
assumes a0:"i < length (locals_' s)" and
        a1:"s \<in> Invariant B adds rems i" and        
        a3:"port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i" and         
        a6:"p_queuing conf (communication_' s) (pt (locals_' s ! i))" and
        a7:"port_open (communication_' s) (pt (locals_' s ! i))" and
        a10:"t=s\<lparr>communication_' :=
            port_set_mutex conf
             (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
             (pt (locals_' s
                   [i := (locals_' s ! i)
                    \<lparr>a_que_aux :=
                      set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                      (add_mset (msg (locals_' s ! i))
                        (get_que_aux conf  (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !i)) 0,
           locals_' := locals_' s [i := (locals_' s
                           [i := (locals_' s ! i)
                         \<lparr>a_que_aux := set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                           (add_mset (msg (locals_' s ! i))
                           (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] ! i) \<lparr>ret_n := Suc 0\<rparr>]\<rparr>" 
 shows "channel_messages (port_channel conf (communication_' s) (pt (locals_' s !i))) adds [0..<length (locals_' t)] \<subseteq># 
          channel_messages  (port_channel conf  (communication_' s) (pt (locals_' s !i))) a_que_aux (locals_' t)"  
proof-  
  have a10':
      "t=s\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
               (pt (locals_' s !i)) 0,
             locals_' := locals_' s [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"    
    using a10 a0 by auto
  then have pt:"pt (locals_' s ! i) = pt (locals_' t ! i)" 
    using a0 by auto
  let ?ch = "port_channel conf (communication_' s) (pt (locals_' s!i))"
  have port_in_channel:
   "port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ?ch "
     using a0 a1 a7  port_exist_unique_channel port_channel 
     unfolding Invariant_def  by fast  
   have state:
     "state_conf s" using a0 a1 unfolding Invariant_def by auto   
   have r_aux_sub:" channel_messages ?ch rems [0..<length (locals_' s)] \<subseteq>#
          channel_messages ?ch r_que_aux (locals_' s)"
     using a1 unfolding Invariant_def by auto
   have a_aux_sub:" channel_messages ?ch adds [0..<length (locals_' s)] \<subseteq>#
          channel_messages ?ch a_que_aux (locals_' s)"
     using a1 unfolding Invariant_def by auto
   have 
     channel_spec:"channel_spec B adds rems ?ch s"  and
     a0':"(s,t,i) \<in> preserves_locals_constr" and       
     a4:"a_que_aux ((locals_' t)!i) ?ch = a_que_aux ((locals_' s)!i) ?ch + ({# (msg (locals_' s ! i)) #})" and 
     a5:"(\<forall>j. j\<noteq>?ch \<longrightarrow> a_que_aux ((locals_' t)!i) j = a_que_aux ((locals_' s)!i) j) \<and>
         r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' t)!i)"  
     using  a1  a3  a6   
           transit_send_que_preserve_locals [OF a0 state a7 port_in_channel _ _ a10']    
     unfolding Invariant_def by auto
    show ?thesis
      using add_channel_message_evnt[OF a0 a0',of a_que_aux,OF a4] 
       a0'  preserves_locals_D1 pt a_aux_sub
      by (metis mset_subset_eq_add_left subset_mset.add_increasing2 subset_mset.le_add_same_cancel1) 
   qed    *)
 
(* lemma insert_queue_preserves_aux_subset:
assumes a0:"i < length (locals_' s)" and
        a1:"s \<in> Invariant B adds rems i" and        
        a3:"port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i" and         
        a6:"p_queuing conf (communication_' s) (pt (locals_' s ! i))" and
        a7:"port_open (communication_' s)  (pt (locals_' s ! i))" and
        a10:"t=s\<lparr>communication_' :=
            port_set_mutex conf
             (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
             (pt (locals_' s
                   [i := (locals_' s ! i)
                    \<lparr>a_que_aux :=
                      set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                      (add_mset (msg (locals_' s ! i))
                        (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !i)) 0,
           locals_' := locals_' s [i := (locals_' s
                           [i := (locals_' s ! i)
                         \<lparr>a_que_aux := set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                           (add_mset (msg (locals_' s ! i))
                           (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] ! i) \<lparr>ret_n := Suc 0\<rparr>]\<rparr>" 
 shows "t\<in>\<lbrace>channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) r_que_aux \<acute>locals \<and>
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) a_que_aux \<acute>locals\<rbrace>"  
proof-  
  have a10':
      "t=s\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
               (pt (locals_' s !i)) 0,
             locals_' := locals_' s [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"    
    using a10 a0 by auto
  then have pt:"pt (locals_' s ! i) = pt (locals_' t ! i)" and 
    ports:"ports (communication_' s) = ports (communication_' t)"
    using a0 unfolding port_set_mutex_def port_insert_message_def Let_def
      by auto
  let ?ch = "port_channel conf (communication_' s) (pt (locals_' s!i))"
  have port_in_channel:
   "port_in_channel conf (communication_' s) (pt (locals_' s ! i)) ?ch "
     using a0 a1 a7   port_exist_unique_channel port_channel 
     unfolding Invariant_def  by fast  
   have state:
     "state_conf s" using a0 a1 unfolding Invariant_def by auto   
   have r_aux_sub:" channel_messages ?ch rems [0..<length (locals_' s)] \<subseteq>#
          channel_messages ?ch r_que_aux (locals_' s)"
     using a1 unfolding Invariant_def by auto
   have a_aux_sub:"channel_messages ?ch adds [0..<length (locals_' s)] \<subseteq>#
          channel_messages ?ch a_que_aux (locals_' s)"
     using a1 unfolding Invariant_def by auto
   have 
     channel_spec:"channel_spec B adds rems ?ch s"  and
     a0':"(s,t,i) \<in> preserves_locals_constr" and       
     a4:"a_que_aux ((locals_' t)!i) ?ch = a_que_aux ((locals_' s)!i) ?ch + ({# (msg (locals_' s ! i)) #})" and 
     a5:"(\<forall>j. j\<noteq>?ch \<longrightarrow> a_que_aux ((locals_' t)!i) j = a_que_aux ((locals_' s)!i) j) \<and>
         r_que_aux ((locals_' s)!i) = r_que_aux ((locals_' t)!i)"  
     using  a1  a3  a6   
           transit_send_que_preserve_locals [OF a0 state a7 port_in_channel _ _ a10']    
     unfolding Invariant_def by auto
    have "channel_messages ?ch adds [0..<length (locals_' t)] \<subseteq>#
    channel_messages ?ch a_que_aux (locals_' t)"
      by (metis a0 a0' a4 a_aux_sub add_channel_message_evnt mset_subset_eq_add_left preserves_locals_D1  
                subset_mset.add_increasing2 subset_mset.le_add_same_cancel1)
    moreover have 
      "channel_messages ?ch rems [0..<length (locals_' t)] \<subseteq>#
       channel_messages ?ch r_que_aux (locals_' t)"
    using a0' a4 add_channel_message_not_evnt preserves_locals_D1 pt r_aux_sub
    using a5 by fastforce 
  moreover have"port_channel conf (communication_' t) (pt (locals_' t ! i)) = 
                port_channel conf (communication_' s) (pt (locals_' t ! i))"
    using port_channl_eq_ports[OF ports, THEN sym, of i, simplified pt] by auto
    ultimately show ?thesis using pt ports by auto
   qed         
     *)
     
lemma tran_insert_state_conf: 
      "state_conf  s \<Longrightarrow>              
       t=s\<lparr>communication_' := 
             port_set_mutex conf 
               (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
               (pt (locals_' s !i)) 0,
             locals_' := (locals_' s) [i := (locals_' s ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                            (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr> \<Longrightarrow>
       state_conf  t"  
  unfolding  state_conf_def channel_set_mutex_def port_set_mutex_def 
           port_insert_message_def Let_def port_exists_def channel_insert_message_def
            channel_set_messages_def chan_queuing_def chan_sampling_def                 
  apply (cases "data (the (chans (communication_' s) (port_channel conf (communication_' s) (pt (locals_' s ! i)))))")    
   by auto

lemma eq_insert: "s\<lparr>communication_' :=
                port_set_mutex conf
                 (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
                 (pt ((locals_' s)
                      [i := (locals_' s ! i)
                         \<lparr>a_que_aux :=
                            set_que_aux conf
                             (port_insert_message conf (communication_' s) (pt (locals_' s ! i) )
                               (msg (locals_' s ! i)) x)
                             (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                             (add_mset (msg (locals_' s ! i))
                               (get_que_aux conf
                                 (port_insert_message conf (communication_' s) (pt (locals_' s ! i))
                                   (msg (locals_' s ! i)) x)
                                 (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                      i))
                 0,
                locals_' := (locals_' s)
                  [i := ((locals_' s)
                         [i := (locals_' s ! i)
                            \<lparr>a_que_aux :=
                               set_que_aux conf
                                (port_insert_message conf (communication_' s) (pt (locals_' s ! i))
                                  (msg (locals_' s ! i)) x)
                                (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                                (add_mset (msg (locals_' s ! i))
                                  (get_que_aux conf
                                    (port_insert_message conf (communication_' s) (pt (locals_' s ! i))
                                      (msg (locals_' s ! i)) x)
                                    (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                         i)
                     \<lparr>ret_n := Suc 0\<rparr>]\<rparr> = 
         s\<lparr>communication_' :=
             port_set_mutex conf
              (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
              (pt ((locals_' s)
                   [i := (locals_' s ! i)
                      \<lparr>a_que_aux :=
                         set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                          (add_mset (msg (locals_' s ! i))
                            (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                   i))
              0,
             locals_' := (locals_' s)
               [i := ((locals_' s)
                      [i := (locals_' s ! i)
                         \<lparr>a_que_aux :=
                            set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                             (add_mset (msg (locals_' s ! i))
                               (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                      i)
                  \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"  
  unfolding set_que_aux_def get_que_aux_def
           Let_def port_insert_message_def port_exists_def                                  
     port_channel_def port_in_channel_def  port_id_name_def
by auto  
  
      
lemma insert_queue_preserves_inv:
        "i < procs conf \<Longrightarrow>
         s \<in> Invariant B adds rems i \<Longrightarrow>         
         port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i \<Longrightarrow>
         evnt (locals_' s ! i) = Send_Message_Q \<Longrightarrow>
         p_source conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
         p_queuing conf  (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>         
         port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
         \<not> port_full conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
         s\<lparr>communication_' :=
             port_set_mutex conf
              (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
              (pt ((locals_' s)
                   [i := (locals_' s ! i)
                      \<lparr>a_que_aux :=
                         set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                          (add_mset (msg (locals_' s ! i))
                            (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                   i))
              0,
             locals_' := (locals_' s)
               [i := ((locals_' s)
                      [i := (locals_' s ! i)
                         \<lparr>a_que_aux :=
                            set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                             (add_mset (msg (locals_' s ! i))
                               (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                      i)
                  \<lparr>ret_n := Suc 0\<rparr>]\<rparr>
         \<in> Invariant B adds rems i" 
  apply (frule procs_len_locals,assumption)
  unfolding Invariant_def     
    apply rule
  using tran_insert_state_conf  
  using insert_queue_preserves_ch_spec[of i s B adds rems Send_Message_Q "s\<lparr>communication_' :=
           port_set_mutex conf (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
            (pt ((locals_' s)
                 [i := (locals_' s ! i)
                    \<lparr>a_que_aux :=
                       set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                        (add_mset (msg (locals_' s ! i)) (get_que_aux conf  (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                 i))
            0,
           locals_' := (locals_' s)
             [i := ((locals_' s)
                    [i := (locals_' s ! i)
                       \<lparr>a_que_aux :=
                          set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                           (add_mset (msg (locals_' s ! i)) (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                    i)
                \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"]       
   apply auto   
      unfolding Invariant_def  by fastforce      

     
lemma send_message_clear_mutex_temp_msg_guar:
    "i < procs conf \<Longrightarrow>
          state_conf s \<Longrightarrow>
          port_get_mutex conf (communication_' s) (pt (locals_' s ! i)) = Suc i \<Longrightarrow>          
          p_source conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
          p_queuing conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
         port_open (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>
         \<not> port_full conf (communication_' s) (pt (locals_' s ! i)) \<Longrightarrow>   
         t= s\<lparr>communication_' :=
                    port_set_mutex conf
                     (port_insert_message conf (communication_' s) (pt (locals_' s ! i)) (msg (locals_' s ! i)) x)
                     (pt ((locals_' s)
                          [i := (locals_' s ! i)
                             \<lparr>a_que_aux :=
                                set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                                 (add_mset (msg (locals_' s ! i))
                                   (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                          i))
                     0,
                    locals_' := (locals_' s)
                      [i := ((locals_' s)
                             [i := (locals_' s ! i)
                                \<lparr>a_que_aux :=
                                   set_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))
                                    (add_mset (msg (locals_' s ! i))
                                      (get_que_aux conf (communication_' s) (pt (locals_' s ! i)) (a_que_aux (locals_' s ! i))))\<rparr>] !
                             i)
                         \<lparr>ret_n := Suc 0\<rparr>]\<rparr> \<Longrightarrow>
    (Normal s, Normal t) \<in> Guarantee_Send_Receive i"     
   unfolding Guarantee_Send_Receive_def    Guarantee_Send_Receive'_def
             port_get_mutex_def channel_get_mutex_def set_que_aux_def get_que_aux_def channel_set_messages_def 
          channel_insert_message_def Let_def port_insert_message_def channel_set_mutex_def 
          port_set_mutex_def state_conf_def Invariant_def chan_queuing_def chan_sampling_def
          channel_get_messages_def port_full_def channel_full_def
             channel_get_bufsize_def  Guarantee_mod_chan_def  
             p_queuing_def   ch_id_queuing_def  port_exists_def  
        apply (case_tac "data (the (chans (communication_' s)
             (port_channel conf  (communication_' s) (pt (locals_' s ! i)))))")   
       unfolding port_channel_def port_in_channel_def  port_id_name_def port_exists_def
    apply auto
   using port_channel_get_channel 
   unfolding state_conf_def chan_queuing_def port_open_def chan_sampling_def not_less_eq_eq 
     port_channel_def port_in_channel_def port_name_in_channel_def port_id_name_def port_exists_def
   by blast                
    

    
lemma sta_cond: "LocalRG_HoareDef.Sta
     (\<lbrace>port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow> \<not> port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"  
  unfolding  Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def  port_id_in_part_def port_open_def 
    Let_def port_channel_def port_in_channel_def port_id_name_def
    p_source_def p_queuing_def port_exists_def
  by fastforce
    
lemma sta_cond_inv:"i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Invariant B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Ev\<rbrace> \<inter>
      \<lbrace>port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow> \<not> port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)" 
  using sta_cond sta_event_inv by (fastforce intro:Sta_intro)

      
lemma sta_not_cond:"LocalRG_HoareDef.Sta 
      (- \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
  unfolding Sta_def apply clarify
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  apply auto
  apply (metis (no_types) option.sel option.simps(3))
 unfolding   Rely_Send_ReceiveQ_def 
  by fastforce+
    
 lemma sta_not_cond_inv:"i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Invariant B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Ev\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
   using sta_not_cond sta_event_inv by (fastforce intro:Sta_intro) 
     
lemma sta_not_cond_inv_mut:
 "LocalRG_HoareDef.Sta
     (\<lbrace>p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and> 
       port_open \<acute>communication (pt (\<acute>locals ! i))  \<rbrace> \<inter>
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (Rely_Send_ReceiveQ i)"     
  unfolding Sta_def apply clarify
  apply simp
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def 
   port_open_def p_source_def
  apply auto
   apply fastforce
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def  
      port_get_mutex_def channel_get_mutex_def port_exists_def
    port_channel_def port_in_channel_def port_id_name_def   
  by fastforce
    
lemma sta_not_cond_inv_mut1:
 "i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Invariant B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Ev\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (Rely_Send_ReceiveQ i)"   
    by (auto intro: subst[of "Invariant B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = Ev\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
      (\<lbrace>p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<and> port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>  \<inter> 
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)"]
       dest:  Sta_intro[OF sta_not_cond_inv sta_not_cond_inv_mut])

lemma send_correct:
  "i < procs conf \<Longrightarrow>
   \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> send_q_message_i i sat [Invariant B adds rems i  \<inter>
                          \<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>, Rely_Send_ReceiveQ i, 
                          Guarantee_Send_Receive  i, Post_Arinc_i B adds rems i,UNIV]"    
apply (auto simp add: Norm_def send_q_message_i_def reflexive_Guarantee_Send 
                                  Int_assoc Post_Arinc_i_def)
apply (rule If,(auto simp add: reflexive_Guarantee_Send))
    apply (rule sta_event_inv, simp+)
     apply (rule conseqPre[where p'="Invariant B adds rems i"]) 
    apply (rule Basic)    
       apply (rule  sta_invariant_rely_send, assumption)+    
     apply(simp add: modify_ret_n_guarantee Invariant_def)    
    apply (auto simp add: modify_ret_inv)                    
apply (rule Seq[where q="Invariant B adds rems i \<inter>
                                    (\<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) \<inter>
                                    - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
                                        (pt (\<acute>locals ! i)) \<longrightarrow>
                                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                     \<not> snd (msg (\<acute>locals ! i)) \<le> 
                                       port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>  \<inter> 
                                      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
            (auto simp add: reflexive_Guarantee_Send))
   apply (rule sta_uni sta_not_cond_inv, assumption?)+
 apply (rule Await)           
    apply (rule sta_uni sta_not_cond_inv sta_not_cond_inv_mut1, assumption?)+
   apply vcg                       
   apply (auto intro:  port_get_set_mutex)[1]   
    apply (simp add: modify_mutex_send_guarantee Invariant_def )
       apply (rule modify_mut_inv, assumption+,simp)   
      apply (auto simp add:   
        port_id_in_part_def p_source_def channel_id_get_source_def port_name_in_channel_def
        port_channel_def port_in_channel_def
        port_id_name_def port_exists_def Let_def port_set_mutex_def p_queuing_def 
        port_open_def port_max_size_def)[5]       
  apply (rule Await)
     apply (rule sta_uni sta_invariant_rely_send sta_not_cond_inv_mut1, assumption?)+ 
  apply vcg
  apply (auto simp add: eq_insert)
     apply (simp add: modify_ret_mutex_zero_guarantee Invariant_def)
     apply (auto simp add:modify_mut_zero_ret_inv)
   apply (simp add: send_message_clear_mutex_temp_msg_guar Invariant_def)[1]
  by (auto simp add: current_def  insert_queue_preserves_inv)
                         
    
lemma modify_ret_QueCom:"i< procs conf \<Longrightarrow> 
      x \<in> Pre_QueCom_ch B adds rems ch_id \<Longrightarrow> 
      x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := m\<rparr>]\<rparr> \<in>  Pre_QueCom_ch B adds rems ch_id" 
proof-
  let ?x' = "x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := m\<rparr>]\<rparr>"
    let ?ch_id = "port_channel conf (communication_' x) (pt(locals_' x!i))"
   assume a0:"i< procs conf" and
         a1:"x\<in>Pre_QueCom_ch B adds rems ch_id"
   then have a0':"i<length (locals_' x)" unfolding Pre_QueCom_ch_def state_conf_def by auto
   have b0:"(x, ?x', i) \<in> preserves_locals_constr" and
        b1:"a_que_aux (locals_' x ! i) = a_que_aux (locals_' ?x' ! i)" and
        b2:"r_que_aux (locals_' x ! i) = r_que_aux (locals_' ?x' ! i)" and
        b3:"chans (communication_' x) = chans (communication_' ?x')" and
        b4:"ports (communication_' x) = ports (communication_' ?x')"         
     using ret_chan_preserves_locals[OF a0'] by auto       
   have pts:"\<forall>i. pt (locals_' x ! i) = pt (locals_' ?x' ! i)" using b0
     using preserves_locals_D2 preserves_locals_D3 by fastforce
   have auxs:"(\<forall>i.(a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' ?x' !i) ch_id) \<and> 
       (r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' ?x' !i) ch_id) )"
     by (metis aux_eq b0 b1 b2) 
   thus ?thesis     
     using  pre_quecom_ch[OF a0 _ _ _ b4 preserves_locals_D1[OF b0] pts auxs a1]          
     by auto
 qed
   
lemma modify_mut_QueCom:
   "i< procs conf \<Longrightarrow> 
   state_conf x \<Longrightarrow>
   port_open (communication_' x)(pt (locals_' x ! i)) \<Longrightarrow>   
    x \<in> Pre_QueCom_ch B adds rems ch_id \<Longrightarrow>  
   x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) (Suc i)\<rparr> \<in> Pre_QueCom_ch B adds rems ch_id"
   proof-
  let ?x' = "x\<lparr>communication_' := 
         port_set_mutex conf (communication_' x) (pt (locals_' x ! i)) (Suc i)\<rparr>"
    let ?ch_id = "port_channel conf  (communication_' x) (pt(locals_' x!i))"
    assume a0:"i< procs conf" and a0':"state_conf x" and
           a1':"port_open (communication_' x)(pt (locals_' x ! i))" and
         a1:"x\<in>Pre_QueCom_ch B adds rems ch_id"
   have p:"port_in_channel conf (communication_' x) (pt (locals_' x ! i)) ?ch_id" 
     using a1 port_unique_channel[OF _ a1'] unfolding Pre_QueCom_ch_def  by auto
   have b0:"(x, ?x', i) \<in> preserves_locals_constr" and
        b0':"(x, ?x', ?ch_id) \<in> preserves_comm_constr" and
        b1:"a_que_aux (locals_' x ! i) = a_que_aux (locals_' ?x' ! i)" and
        b2:"r_que_aux (locals_' x ! i) = r_que_aux (locals_' ?x' ! i)"   
     using modify_mutex_preserves_locals[OF a0' a1' p] by auto               
   have pts:"\<forall>i. pt (locals_' x ! i) = pt (locals_' ?x' ! i)" using b0
     using preserves_locals_D2 preserves_locals_D3 by fastforce
   have auxs:"(\<forall>i.(a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' ?x' !i) ch_id) \<and> 
       (r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' ?x' !i) ch_id) )"
     by (metis aux_eq b0 b1 b2)        
   thus ?thesis     
     using  pre_quecom_ch[OF a0 _ _ _  _ preserves_locals_D1[OF b0] pts auxs a1]  b0'
     unfolding port_set_mutex_def Let_def channel_set_mutex_def chan_queuing_def chan_sampling_def     
       preserves_comm_constr_def
     by auto
 qed
   
lemma modify_mut_zero_ret_QueCom:
   "i<procs conf \<Longrightarrow>
   x \<in> Pre_QueCom_ch B adds rems ch_id \<Longrightarrow>   
   port_get_mutex conf (communication_' x) (pt (locals_' x ! i)) = Suc i \<Longrightarrow>
    port_open (communication_' x) (pt (locals_' x!i)) \<Longrightarrow>   
   x\<lparr>locals_' := (locals_' x)[i := (locals_' x ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt ((locals_' x)[i := ((locals_' x) ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>
       \<in> Pre_QueCom_ch B adds rems ch_id"
   proof-
  let ?x' = "x\<lparr>locals_' := (locals_' x)[i := ((locals_' x) ! i)\<lparr>ret_n := Suc 0\<rparr>],
     communication_' :=
           port_set_mutex conf (communication_' x) (pt ((locals_' x)[i := ((locals_' x) ! i)\<lparr>ret_n := Suc 0\<rparr>] ! i)) 0\<rparr>"
    let ?ch_id = "port_channel conf (communication_' x) (pt(locals_' x!i))"
    assume a0:"i< procs conf" and
           a1':"port_open (communication_' x) (pt (locals_' x!i))" and               
         a1:"x\<in>Pre_QueCom_ch B adds rems ch_id"     
    then have a0':"i<length (locals_' x)" unfolding Pre_QueCom_ch_def state_conf_def by auto 
   have p:"port_in_channel conf (communication_' x) (pt (locals_' x ! i)) ?ch_id" 
     using a1 port_unique_channel[OF _ a1'] unfolding Pre_QueCom_ch_def  by auto
   have b0:"(x, ?x', i) \<in> preserves_locals_constr" and
        b0':"(x, ?x', ?ch_id) \<in> preserves_comm_constr" and
        b1:"a_que_aux (locals_' x ! i) = a_que_aux (locals_' ?x' ! i)" and
        b2:"r_que_aux (locals_' x ! i) = r_que_aux (locals_' ?x' ! i)"   
     using modify_mutex_ret_preserves_locals[OF a0' _ a1' p] a1[simplified Pre_QueCom_ch_def] by auto               
   have pts:"\<forall>i. pt (locals_' x ! i) = pt (locals_' ?x' ! i)" using b0
     using preserves_locals_D2 preserves_locals_D3 by fastforce
   have auxs:"(\<forall>i.(a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' ?x' !i) ch_id) \<and> 
       (r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' ?x' !i) ch_id) )"
     by (metis aux_eq b0 b1 b2)        
   thus ?thesis     
     using  pre_quecom_ch[OF a0 _ _ _  _ preserves_locals_D1[OF b0] pts auxs a1]  b0'
     unfolding port_set_mutex_def Let_def channel_set_mutex_def chan_queuing_def chan_sampling_def     
       preserves_comm_constr_def
     by auto
 qed
    
lemma insert_queue_preserves_QueCom:
  assumes a0:"i < procs conf" and
         a1:"x \<in> Pre_QueCom_ch B adds rems ch_id" and
         a2:" port_open (communication_' x) (pt (locals_' x!i))" and        
         a3:"x' = x\<lparr>communication_' :=
             port_set_mutex conf
              (port_insert_message conf (communication_' x) (pt (locals_' x ! i)) (msg (locals_' x ! i)) t)
              (pt ((locals_' x)
                   [i := (locals_' x ! i)
                      \<lparr>a_que_aux :=
                         set_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))
                          (add_mset (msg (locals_' x ! i))
                            (get_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))))\<rparr>] !
                   i))
              0,
             locals_' := (locals_' x)
               [i := ((locals_' x)
                      [i := (locals_' x ! i)
                         \<lparr>a_que_aux :=
                            set_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))
                             (add_mset (msg (locals_' x ! i))
                               (get_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))))\<rparr>] !
                      i)
                  \<lparr>ret_n := Suc 0\<rparr>]\<rparr>"          
   shows  "x' \<in> Pre_QueCom_ch B adds rems ch_id"  
proof-   
    let ?ch_id = "port_channel conf  (communication_' x) (pt(locals_' x!i))"        
    have a0':"i<length (locals_' x)" using a0 a1 unfolding Pre_QueCom_ch_def state_conf_def by auto    
    then have eq_s':"x' = x\<lparr>communication_' := 
             port_set_mutex conf
               (port_insert_message conf (communication_' x) (pt (locals_' x ! i)) (msg (locals_' x ! i)) t)
               (pt (locals_' x !i)) 0,
             locals_' := (locals_' x) [i := (locals_' x ! i)
                         \<lparr>a_que_aux := 
                           set_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))
                            (add_mset (msg (locals_' x ! i))
                                      (get_que_aux conf (communication_' x) (pt (locals_' x ! i)) (a_que_aux (locals_' x ! i))))\<rparr>  
                        \<lparr>ret_n := Suc 0\<rparr>]\<rparr>" using a3 by auto      
   have p:"port_in_channel conf (communication_' x) (pt (locals_' x ! i)) ?ch_id" 
     using a1 port_unique_channel[OF _ a2] unfolding Pre_QueCom_ch_def  by auto
   have b0:"(x, x', i) \<in> preserves_locals_constr" and
        b0':"(x, x', ?ch_id) \<in> preserves_comm_constr" and
        b1:"(\<forall>j. j\<noteq> ?ch_id \<longrightarrow> a_que_aux ((locals_' x')!i) j = a_que_aux ((locals_' x)!i) j)" and
        b2:"r_que_aux (locals_' x ! i) = r_que_aux (locals_' x' ! i)"   
     using transit_send_que_preserve_locals'[OF a0' _ a2 p eq_s'] 
           a1[simplified Pre_QueCom_ch_def]by auto              
   have pts:"\<forall>i. pt (locals_' x ! i) = pt (locals_' x' ! i)" using b0
     using preserves_locals_D2 preserves_locals_D3 by fastforce
             
   have chans:" chans (communication_' x) ?ch_id \<noteq> chans (communication_' x') ?ch_id \<longrightarrow>
    (\<forall>chs. chans (communication_' x) ?ch_id = Some chs \<longrightarrow>
           (\<exists>chs'. chans (communication_' x') ?ch_id = Some chs' \<and> chan_queuing chs = chan_queuing chs'))"
     using eq_s' unfolding port_set_mutex_def port_insert_message_def Let_def channel_insert_message_def
       channel_set_messages_def  channel_set_mutex_def chan_queuing_def chan_sampling_def 
       port_channel_def port_in_channel_def port_id_name_def port_exists_def
     apply auto apply (case_tac "data chs") apply auto   
       apply (case_tac "data chs") 
     by auto
   show ?thesis     
     using  pre_quecom_ch'[OF a0 _ _ chans  _ preserves_locals_D1[OF b0] pts _]  b0'
     unfolding port_set_mutex_def Let_def channel_set_mutex_def chan_queuing_def chan_sampling_def     
       preserves_comm_constr_def port_insert_message_def channel_insert_message_def
     using a1 b0 b1 b2 preserves_locals_D2 by fastforce     
 qed
   
lemma sta_cond_spec:"LocalRG_HoareDef.Sta 
      ( \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
  unfolding Sta_def apply clarify
  apply (frule rely_eq_ports1)
  unfolding 
     p_queuing_def   port_exists_def
    port_channel_def port_in_channel_def port_id_name_def port_open_def
    p_source_def  port_id_in_part_def port_max_size_def port_id_in_part_def
  by fastforce
   
    
lemma sta_cond_PreQue:"i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Pre_QueCom_ch B adds rems ch_id \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace> \<inter>
      \<lbrace>port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
       p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
       p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow> \<not> port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)" 
  using sta_cond sta_event_inv_PreQue by (fastforce intro:Sta_intro)
     
 lemma sta_not_cond_inv_PreQue:"i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Pre_QueCom_ch B adds rems ch_id \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>)
     (Rely_Send_ReceiveQ i)"
   using sta_not_cond sta_event_inv_PreQue by (fastforce intro:Sta_intro)     
    
lemma sta_not_cond_inv_mut1_PreQue:
 "i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta
     (Pre_QueCom_ch B adds rems ch_id \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>)
     (Rely_Send_ReceiveQ i)"   
    by (auto intro: subst[of "(Pre_QueCom_ch B adds rems ch_id \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace> \<inter>
      - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i))) (pt (\<acute>locals ! i)) \<longrightarrow>
         p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
         \<not> snd (msg (\<acute>locals ! i)) \<le> port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>
      (\<lbrace>p_source conf \<acute>communication (pt (\<acute>locals ! i))\<and> port_open \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter> 
       \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace>))"]
       dest:  Sta_intro[OF sta_not_cond_inv_PreQue sta_not_cond_inv_mut])      


     
lemma send_correct':
  " i < Sys_Config.procs conf \<Longrightarrow>
    \<Gamma>,{} \<turnstile>\<^bsub>/{}\<^esub> send_q_message_i i sat [Pre_QueCom_ch B adds rems ch_id \<inter>
                           \<lbrace>evnt (\<acute>locals ! i) =
                            Send_Message_Q\<rbrace>, Rely_Send_ReceiveQ
                                              i, Guarantee_Send_Receive i, Pre_QueCom_ch B adds rems ch_id,UNIV]"    
 apply (auto simp add: Norm_def send_q_message_i_def reflexive_Guarantee_Send 
                                  Int_assoc )
apply (rule If,(auto simp add: reflexive_Guarantee_Send))
    apply (rule sta_event_inv_PreQue, assumption)
   apply (rule conseqPre[where p'="Pre_QueCom_ch B adds rems ch_id"])            
    apply (rule Basic)       
           apply (rule sta_cond_PreQue sta_no_channel_rely_send, assumption)+
    apply(simp add: modify_ret_n_guarantee Pre_QueCom_ch_def)        
     apply (auto simp add: modify_ret_QueCom )             
apply (rule Seq[where q="Pre_QueCom_ch B adds rems ch_id \<inter>
                                    (\<lbrace>evnt (\<acute>locals ! i) = Send_Message_Q\<rbrace>) \<inter>
                                    - \<lbrace>port_open \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                      port_id_in_part conf \<acute>communication (current (schedule (\<acute>locals ! i)))
                                        (pt (\<acute>locals ! i)) \<longrightarrow>
                                      p_source conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                      p_queuing conf \<acute>communication (pt (\<acute>locals ! i)) \<longrightarrow>
                                     \<not> snd (msg (\<acute>locals ! i)) \<le> 
                                       port_max_size conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace>  \<inter> 
                                      \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = (Suc i)\<rbrace>"], 
            (auto simp add: reflexive_Guarantee_Send))
   apply (rule sta_uni sta_not_cond_inv_PreQue, assumption?)+
 apply (rule Await)           
      apply (rule sta_uni sta_not_cond_inv_PreQue sta_not_cond_inv_mut1_PreQue, assumption?)+        
 apply vcg                        
 apply (auto simp add:  current_def port_get_set_mutex)[1]
    apply (simp add: modify_mutex_send_guarantee Pre_QueCom_ch_def)
    apply (rule modify_mut_QueCom, assumption+, simp add:Pre_QueCom_ch_def, assumption+)    
    apply (auto simp add:   
        port_id_in_part_def p_source_def channel_id_get_source_def port_name_in_channel_def
        port_channel_def port_in_channel_def
        port_id_name_def port_exists_def Let_def port_set_mutex_def p_queuing_def port_open_def port_max_size_def)[5] 
  apply (rule Await)
         apply (rule sta_uni sta_no_channel_rely_send sta_not_cond_inv_mut1_PreQue, assumption?)+
  apply vcg
  apply (auto simp add: eq_insert)
     apply (simp add: modify_ret_mutex_zero_guarantee Pre_QueCom_ch_def)
    apply (auto simp add: current_def modify_mut_zero_ret_QueCom)
    apply (simp add:  send_message_clear_mutex_temp_msg_guar Pre_QueCom_ch_def)
  by (auto simp add: insert_queue_preserves_QueCom)


   
 
end      
  