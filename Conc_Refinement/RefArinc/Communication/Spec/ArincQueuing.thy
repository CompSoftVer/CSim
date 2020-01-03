theory ArincQueuing
 imports "../../ArincMultiCoreState" 
begin
subsection {* channel messages *}
text {*
messages on channels definition for management of auxiliary variables
To get track of messages added and removed to/from a channel 
messages are stored in an auxiliary variable. The queue for a channel ch
is always equal to the initial value of the queue plus the auxiliary variables
of the processes sending a message to the channel, minus the auxiliary variables
of the processes removing/clearing messages from the channel. *}

lemma (in semigroup) foldl_assoc:
   "foldl f (f x y) zs = f x (foldl f y zs)"
   by (induct zs arbitrary: y) (simp_all add:assoc)

lemma (in monoid) foldl_absorb1:
  "f x (foldl f z zs) = foldl f x zs"
  by (induct zs) (simp_all add:foldl_assoc)

definition channel_messages :: "channel_id  \<Rightarrow> ('a \<Rightarrow> (channel_id \<Rightarrow> Message multiset)) \<Rightarrow> 
                                  'a list \<Rightarrow> Message multiset"
where
"channel_messages ch_id aux ls  \<equiv>       
      fold (\<lambda>m ms. ms + m)  [((aux i) ch_id). i <-ls] {#}
"

lemma union_fold: 
  "fold (\<lambda>m ms. ms + m)  ((l::'a multiset)#ls) s = (l::'a multiset) + (fold (\<lambda>m ms. ms + m)  ls s)"
proof -
  have "\<forall>ms m ma. foldl (+) ((ma::'a multiset) + m) ms = foldl (+) ma ms + m"  
    using union_commute
    by (auto simp add: add.foldl_assoc union_commute)
  then have "foldl (+) s (l # ls) = foldl (+) s ls + l"
    by simp
  then show ?thesis
    by (simp add: foldl_conv_fold union_commute)
qed

lemma concat_fold1:
  "fold (\<lambda>m ms. ms + m)  ((l1::'a multiset list)@l2) s = fold (\<lambda>m ms. ms + m)  l1 {#} + 
                                                         fold (\<lambda>m ms. ms + m) l2 s"
proof (induct l1)
  case Nil thus ?case by auto
next
  case (Cons l l1)
  thus ?case
    by (metis (full_types) append_Cons union_commute union_fold union_lcomm)
qed

lemma same_channel_messages:
  "(\<forall>i<length ls.         
           (aux (ls'!i)) ch_id = (aux (ls!i)) ch_id) \<Longrightarrow>
      length ls = length ls' \<Longrightarrow> 
 (channel_messages ch_id aux ls ) = (channel_messages  ch_id aux ls')" 
proof -
 assume a0: "(\<forall>i<length ls.         
               (aux (ls'!i)) ch_id = (aux (ls!i)) ch_id)" and
        a1:"length ls = length ls'" 
 then have  " [((aux i) ch_id). i <-ls] =  [((aux i) ch_id). i <-ls']"    
   by (auto intro: nth_Cons' nth_equalityI)
 thus ?thesis unfolding channel_messages_def by auto
qed

lemma channel_local_s:
"\<not> (x \<in># s) \<Longrightarrow>
 x \<in>#  fold (\<lambda>m ms. ms + m)  [((aux i) ch_id). i <-ls] s \<Longrightarrow>
 \<exists>i. (i<length ls) \<and> x \<in># ((aux (ls!i)) ch_id)
"
proof(induct ls arbitrary: s)
  case Nil then show ?case by auto
next
  case (Cons l ls) 
    then have "x\<in>#  (aux l ch_id) \<or> 
               (\<not>(x\<in>#  (aux l ch_id))) \<and> 
                  x \<in># (fold (\<lambda>m ms. ms + m) (map (\<lambda>i. (aux i ch_id)) (ls))) (s + (aux l ch_id))"
    by auto
    then show ?case proof
      assume "x \<in># (aux l ch_id)" then show ?thesis by auto
    next
      assume ass:
         "(\<not>(x\<in>#  (aux l ch_id))) \<and> 
          x \<in># fold (\<lambda>m ms. ms + m) (map (\<lambda>i. (aux i ch_id)) ls) (s +  (aux l ch_id))"             
      thus ?thesis  
        using Cons(1)[of "(aux l ch_id) + s"] ass Cons(2) by (auto simp add: union_commute)
    qed
qed

lemma in_channel_local: 
  "x \<in># channel_messages ch_id aux ls \<Longrightarrow>    
   \<exists>i. (i<length ls) \<and> x \<in># ((aux (ls!i)) ch_id)"
unfolding channel_messages_def 
using channel_local_s[of x "{#}"] by auto

lemma l1':"s\<subseteq>#s1 \<Longrightarrow>
           s\<subseteq>#fold (\<lambda>m ms. ms + m) ls s1"
proof (induct ls arbitrary: s1)
  case Nil thus ?case by auto
next
  case (Cons l ls)
  then have "s\<subseteq>#s1 + l" 
    using add.commute subset_mset.dual_order.trans
      by (simp add: Cons.prems subset_mset.add_increasing2)    
  moreover have "fold (\<lambda>m ms. ms + m) ls (s1 +  l ) = 
                 fold (\<lambda>m ms. ms + m) (l#ls) s1" by auto
  moreover have "s1 +  l =  l + s1"
    by (simp add: add.commute) 
  ultimately show ?case using Cons(1)[of " l+ s1"] by metis
qed

lemma l1:"s\<subseteq>#s1 \<Longrightarrow>
          s\<subseteq>#fold (\<lambda>m ms. ms + m) (map (\<lambda>i. (aux i ch_id)) ls) s1"
using l1' by auto

lemma channel_in_union: 
  "i<length ls \<Longrightarrow>
    ls!i \<subseteq># fold (\<lambda>m ms. ms + m)  ls s"
proof (induct ls arbitrary: s i)
  case Nil thus ?case by auto
next
  case (Cons l ls)  
  thus ?case proof (cases "(l#ls)!i = l")
    case True
    have f1:" l\<subseteq># s + l" by auto
    have "fold (\<lambda>m ms. ms + m) (l#ls) s = 
               fold (\<lambda>m ms. ms + m) ls (s +  l)" by auto
    then show ?thesis using l1'[OF f1] True by auto
  next
    case False             
    obtain i' where f1:"(l#ls)!i = ls!i' \<and> i'<length ls"
      using Cons.prems False less_Suc_eq_0_disj by auto      
    then have " ls!i' \<subseteq># fold (\<lambda>m ms. ms + m) ls (s +  l)"
      using Cons(1) less_Suc_eq_0_disj by auto
    thus ?thesis using f1 by auto
  qed 
qed

lemma in_set_messages_in_channel: 
  assumes a0:"i<length ls"
  shows "((aux (ls!i)) ch_id) \<subseteq># fold (\<lambda>m ms. ms + m)  [((aux i) ch_id). i <-ls] s"
proof -
  have a0:"i<length [((aux i) ch_id). i <-ls]" using a0 by auto
  have "[((aux i) ch_id). i <-ls]!i = ((aux (ls!i)) ch_id)" using a0 by auto
  then show ?thesis using channel_in_union[OF a0] by auto
qed

lemma i_messages_in_channel: 
  " i<length ls \<Longrightarrow>
   ((aux (ls!i)) ch_id) \<subseteq># channel_messages  ch_id aux ls"
 unfolding channel_messages_def using in_set_messages_in_channel[of i ls ] by auto

lemma union_fold_eq_add_sub:
  assumes a0:"i< length (ls::'a multiset list)"
  shows "fold (\<lambda>m ms. ms + m) ls s = (fold (\<lambda>m ms. ms + m) ls s - ls!i) + ls!i"
 using subset_mset.le_imp_diff_is_add channel_in_union[OF a0] by auto


lemma aux_list_3:
 assumes a0: "i<length ls" and
         a1: "length ls - (i + 1) = k"
 shows "\<exists>ls1 ls2. ls = ls1@[ls!i]@ls2 \<and> length ls1 = i \<and> length ls2 = length ls - i - 1"

using a0 a1  
proof (induct k arbitrary: ls i)
 case 0 thus ?case using take_Suc_conv_app_nth by force   
next
 case (Suc k)      
   then obtain i' where i':"i'=Suc i \<and> i' < length ls" using Suc
     by (metis Suc_eq_plus1 Suc_lessI diff_self_eq_0 less_nat_zero_code zero_less_Suc)
   moreover then have "length ls - (i' + 1) = k" using Suc(3) by auto
   ultimately obtain ls1 ls2 where "ls = ls1 @ [ls ! i'] @ ls2 \<and> length ls1 = i' \<and> length ls2 = length ls - i' - 1"  
     using Suc (1) by fastforce    
   moreover then obtain ls1' where "ls1 = ls1'@[ls!i]"  using i' Suc(2)
     by (metis append_eq_conv_conj hd_drop_conv_nth take_hd_drop) 
   ultimately have "ls = ls1'@[ls!i]@([ls!i']@ls2) \<and> length ls1' = i \<and> 
                    length ([ls!i']@ls2) = length ls - i - 1" using i' by auto
   thus ?case by fastforce
 qed


lemma eq_ls1_ls2:
  assumes a0:"i<length (ls::'a multiset list)" and
     a1: "length ls = length ls'" and
     a2: "\<forall>i'<length ls. i' \<noteq> i \<longrightarrow> ls!i' = ls'!i'"
  shows "\<exists>ls1 ls2. ls = ls1@[ls!i]@ls2 \<and> ls' = ls1@[ls'!i]@ ls2 \<and> 
         length ls1 = i \<and> length ls2 = length ls - i - 1"
proof -
obtain ls1 ls2 where 
  ls1:"ls = ls1@[ls!i]@ls2 \<and> length ls1 = i \<and> length ls2 = length ls - i - 1" 
    using a0 aux_list_3 by metis
  also obtain ls1' ls2' where 
  ls1':"ls' = ls1'@[ls'!i]@ ls2' \<and> length ls1' = i \<and> length ls2' = length ls' - i - 1" using a0 a1 aux_list_3 by metis
  ultimately have "ls1=ls1' \<and> ls2=ls2'"
  proof-
    have ls1_eq_len:"length ls1=length ls1'" using a0 a1 ls1 ls1' by auto
    have ls2_eq_len:"length ls2 = length ls2'" using a0 a1 ls1 ls1' by auto 
    have i_less_ls:"\<forall>i'<i. i'< length ls" using a0 by auto
    have "ls1=ls1'" 
    proof -
      have "\<forall>i'<i. ls1!i' = ls1'!i'" using ls1 ls1' i_less_ls a2
        by (metis cancel_comm_monoid_add_class.diff_cancel not_less0 nth_append zero_less_diff)  
      thus ?thesis using ls1_eq_len ls1 by (simp add: nth_equalityI) 
    qed 
    also have "ls2=ls2'"
    proof -      
      have "\<forall>i'<length ls - i - 1. ls2!i' = ls!(i+i'+1)" 
        using ls1
        by (metis Suc_eq_plus1 add_Suc_right append_Cons append_Nil nth_Cons_Suc nth_append_length_plus)
      also have "\<forall>i'<length ls - i - 1. ls2'!i' = ls'!(i+i'+1)" 
        using ls1'
        by (metis Suc_eq_plus1 add_Suc_right append_Cons append_Nil nth_Cons_Suc nth_append_length_plus)
      ultimately have "\<forall>i'<length ls - i - 1. ls2!i' = ls2'!i'" using a1 a2
        by auto 
      thus ?thesis using ls2_eq_len ls1' ls1 by (simp add: nth_equalityI) 
    qed
    ultimately show ?thesis by auto
  qed
  thus ?thesis using ls1 ls1' by fastforce
qed 


lemma remove_diff_eq:
  assumes a0:"i<length (ls::'a multiset list)" and
     a1: "length ls = length ls'" and
     a2: "\<forall>i'<length ls. i' \<noteq> i \<longrightarrow> ls!i' = ls'!i'" 
  shows "(fold (\<lambda>m ms. ms + m) ls s) - (ls ! i) = (fold (\<lambda>m ms. ms + m) ls' s) - (ls' ! i)"
proof -
  obtain ls1 ls2 where 
   ls:"ls = ls1@(ls!i#ls2) \<and> ls' = ls1@(ls'!i# ls2) \<and> 
    length ls1 = i \<and> length ls2 = length ls - i - 1" using eq_ls1_ls2[OF a0 a1 a2] by auto
  then have "(fold (\<lambda>m ms. ms + m) ls s) = 
     fold (\<lambda>m ms. ms + m)  ls1 {#} + ls!i + fold (\<lambda>m ms. ms + m) ls2 s" 
    using concat_fold1 union_fold by (metis union_assoc) 
  also have "(fold (\<lambda>m ms. ms + m) ls' s) = 
     fold (\<lambda>m ms. ms + m)  ls1 {#} + ls'!i + fold (\<lambda>m ms. ms + m) ls2 s"
    using ls concat_fold1 union_fold by (metis union_assoc)
  ultimately show ?thesis
    by (metis (no_types, lifting) add_implies_diff union_assoc union_commute) 
qed

lemma add_msg_rec:
  assumes a0:"r1 + m = r2" and
          a1:"m \<subseteq># s - (r1 -r0)" and
          a2:"r1 - r0 \<subseteq># s" and
          a3:"r0 \<subseteq># r1" 
  shows "r2 - r0 \<subseteq># s"
using a0 a1 a2 a3 
  by (simp add: subset_mset.le_diff_conv2 union_commute)
    
lemma add_msg_send:
  assumes a0:"r\<subseteq># b + (s1 - s0)" and
          a1:"s0 \<subseteq># s1"                   
  shows "r \<subseteq># b + ((s1+{# m #}) - s0)"
proof -
  have "r - b \<subseteq># s1 - s0 + {#m#}"
    by (metis (no_types) a0 add.commute mset_subset_eq_add_left subset_eq_diff_conv subset_mset.order.trans)
  then show ?thesis
    by (metis a1 add.commute subset_eq_diff_conv subset_mset.diff_add_assoc2)
qed
  
  
lemma same_message_channel:
 assumes 
        a1:"length ls = length ls'" and
        a2:"\<forall>i'. i' \<noteq> i \<longrightarrow> aux_msg (ls ! i') ch = aux_msg (ls' ! i') ch" and
        a3: "aux_msg (ls ! i) ch = aux_msg (ls' ! i) ch" 
 shows
    "channel_messages  ch  aux_msg ls  =
      channel_messages  ch aux_msg ls'"
proof -
  let ?ls="(map (\<lambda>i. aux_msg i ch) ls)"
  let ?ls' = "(map (\<lambda>i. aux_msg i ch) ls')"  
  have a1:"length ?ls = length ?ls'" using a1 by auto
  moreover have a2:"\<forall>i'<length ?ls. ?ls!i' = ?ls'!i'" using  a1 a2 a3 by auto
  ultimately have "?ls = ?ls'" by (auto intro: nth_equalityI) 
  thus ?thesis unfolding channel_messages_def by auto   
qed

lemma add_message_channel:
 assumes a0:"i<length ls" and
        a1:"length ls = length ls'" and
        a2:"\<forall>i'. i' \<noteq> i \<longrightarrow> aux_msg (ls ! i') ch = aux_msg (ls' ! i') ch" and
        a3: "aux_msg (ls' ! i) ch = aux_msg (ls ! i) ch + mess" 
 shows
    "channel_messages  ch  aux_msg ls  + mess =
      channel_messages  ch aux_msg ls'"
unfolding channel_messages_def 
proof -
  let ?ls="(map (\<lambda>i. aux_msg i ch) ls)"
  let ?ls' = "(map (\<lambda>i. aux_msg i ch) ls')"
  have a0:"i<length ?ls" using a0 by auto
  have a1:"length ?ls = length ?ls'" using a1 by auto
  have a2:"\<forall>i'<length ?ls. i' \<noteq> i \<longrightarrow> ?ls!i' = ?ls'!i'" using a0 a1 a2 by auto
  obtain ls1 ls2 where 
   ls:"?ls = ls1@(?ls!i#ls2) \<and> ?ls' = ls1@(?ls'!i# ls2) \<and> 
    length ls1 = i \<and> length ls2 = length ?ls - i - 1" using eq_ls1_ls2[OF a0 a1 a2]  by auto
  have ls_eq:"(fold (\<lambda>m ms. ms + m) ?ls {#}) =  
             fold (\<lambda>m ms. ms + m)  ls1 {#} + ?ls!i + fold (\<lambda>m ms. ms + m) ls2 {#}" and
       ls'_eq:"(fold (\<lambda>m ms. ms + m) ?ls' {#}) =  
             fold (\<lambda>m ms. ms + m)  ls1 {#} + ?ls'!i + fold (\<lambda>m ms. ms + m) ls2 {#}"
    by (metis  ls concat_fold1 union_fold union_assoc)+
  also have ls_map:"?ls!i = aux_msg (ls ! i) ch \<and> ?ls'!i = aux_msg(ls'!i) ch" using a2 a0 a1 by auto
  ultimately show "fold (\<lambda>m ms. ms + m) ?ls {#} + mess = fold (\<lambda>m ms. ms + m) ?ls' {#}"   
  proof -
    have "fold (\<lambda>m ma. ma + m) (map (\<lambda>l. aux_msg l ch) ls) {#} + mess = 
        fold (\<lambda>m ma. ma + m) ls1 {#} + map (\<lambda>l. aux_msg l ch) ls ! i + (fold (\<lambda>m ma. ma + m) ls2 {#} + mess)"
    using ls_eq union_assoc by auto
    then have "fold (\<lambda>m ma. ma + m) (map (\<lambda>l. aux_msg l ch) ls) {#} + mess = 
              fold (\<lambda>m ma. ma + m) ls1 {#} + aux_msg (ls ! i) ch + (mess + fold (\<lambda>m ma. ma + m) ls2 {#})"
      by (simp add:ls_map union_commute)
    then show ?thesis
      by (simp add: a3 ls'_eq ls_map union_assoc)
    qed  
qed


definition channel_sent_messages :: "channel_id \<Rightarrow> (nat \<Rightarrow> channel_id \<Rightarrow> Message multiset) \<Rightarrow> locals list \<Rightarrow> Message multiset"
where                                      
"channel_sent_messages ch_id msgs ls \<equiv> (channel_messages ch_id a_que_aux ls) - (channel_messages ch_id msgs [0..< (length ls)])"
                                             
definition channel_received_messages :: "channel_id \<Rightarrow>(nat => channel_id \<Rightarrow> Message multiset) \<Rightarrow> locals list \<Rightarrow> Message multiset"
where
"channel_received_messages ch_id msgs ls \<equiv> channel_messages  ch_id r_que_aux ls - (channel_messages ch_id msgs [0..< (length ls)])"


definition ch_spec
where
"ch_spec B adds rems ch_id x \<equiv>
 let ch = the (chans (communication_' x) ch_id) in
 channel_get_messages ch = 
  (B ch_id + channel_sent_messages  ch_id  adds (locals_' x) ) -
             channel_received_messages  ch_id  rems (locals_' x) \<and>
  channel_received_messages  ch_id rems (locals_' x) \<subseteq># 
    (B ch_id + channel_sent_messages ch_id adds  (locals_' x)) \<and>
(size (channel_get_messages ch) \<le> 
   channel_size (get_channel conf ch_id))  \<and> 
    channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq># 
    channel_messages  ch_id r_que_aux (locals_' x) \<and>
    channel_messages ch_id adds [0..<length (locals_' x)] \<subseteq># 
    channel_messages  ch_id a_que_aux (locals_' x)"
                        (*x s :==(f s1 s2 s3 s4) s *)
    
lemma "Q s = True \<Longrightarrow> card ({|s.  Q s|}) = 1" 
  by auto
 
 
definition channel_spec
where
"channel_spec B adds rems ch_id s \<equiv> 
   \<forall>ch. 
     (chans (communication_' s) ch_id = Some ch \<and> 
     ch_id_queuing conf ch_id \<longrightarrow>  
       ch_spec B adds rems ch_id s)
"

definition channel_spec_mut
where
"channel_spec_mut B adds rems ch_id s \<equiv> 
   \<forall>ch. 
     (chans (communication_' s) ch_id = Some ch \<and> 
      mut ch = 0 \<and>
     ch_id_queuing conf ch_id \<longrightarrow>  
       ch_spec B adds rems ch_id s)
"


lemma channel_spec_intro:
 "\<forall>ch.  
     (chans (communication_' x) ch_id) = Some ch \<and> 
     ch_id_queuing conf ch_id  \<longrightarrow> 
   ch_spec B adds rems ch_id  x \<Longrightarrow>
  channel_spec B adds rems ch_id x"
unfolding channel_spec_def ch_spec_def by fastforce

lemma channel_spec_dest1:
  "channel_spec B  adds rems ch_id x \<Longrightarrow>
    (chans (communication_' x) ch_id) = Some ch \<and> 
     ch_id_queuing conf ch_id  \<longrightarrow>  
    ch_spec B  adds rems ch_id x"
unfolding channel_spec_def ch_spec_def by fastforce

lemma channel_spec_dest2:
    "channel_spec B  adds rems ch_id x \<Longrightarrow>
    (chans (communication_' x) ch_id) = Some ch \<and> 
     ch_id_queuing conf ch_id  \<Longrightarrow> 
    ch_spec B  adds rems ch_id x"
unfolding channel_spec_def ch_spec_def by fastforce


subsection {*definitions and lemmas on constrainings over local and comm fields
             to preserve channel spec*}
text{* preserves\_locals\_constr establishes local variables to the component and the enviroment
       that cannot modified for correctness of the specification 
       locals: evnt (event being executed); pt (port where the operation is carried out);
               and aux\_msg (auxiliary variable to verify the queue. This does not have necessary 
               to be for all i'. i!=i') as reflected by preserves\_locals\_constr'*}
definition preserves_locals_constr
where
"preserves_locals_constr  \<equiv> 
    {(x,x',i). length (locals_' x) =  length (locals_' x') \<and>
               (\<forall>i'. (i\<noteq>i' \<longrightarrow> evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                                pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                                
                                (a_que_aux ((locals_' x)!i') = a_que_aux ((locals_' x')!i')) \<and>
                                (r_que_aux ((locals_' x)!i') = r_que_aux ((locals_' x')!i'))) \<and>
                     (i=i' \<longrightarrow> evnt ((locals_' x)!i) = evnt ((locals_' x')!i) \<and>
                                pt ((locals_' x)!i) = pt ((locals_' x')!i) ))
   }
"

definition preserves_locals_constr'
where
"preserves_locals_constr'  \<equiv> 
    {(x,x',i). length (locals_' x) =  length (locals_' x') \<and>
               (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                      pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                     
                     a_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i)))  = 
                     a_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i))) \<and>
                      r_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i)))  = 
                      r_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i))) )
   }
"

lemma preserves_locals'_D1:
  "(x,x',i)\<in> preserves_locals_constr' \<Longrightarrow> 
    length (locals_' x) =  length (locals_' x')
  "
 unfolding preserves_locals_constr'_def by auto

lemma preserves_locals'_D2:
  "(x,x',i)\<in> preserves_locals_constr' \<Longrightarrow> 
    (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
          pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                   
         a_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i)))  = 
         a_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i))) \<and>
          r_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i)))  = 
          r_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i))) )
  "
unfolding preserves_locals_constr'_def by fastforce

lemma preserves_locals'_D3:
  "(x,x',i')\<in> preserves_locals_constr' \<Longrightarrow>        
      a_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i')))  = 
     a_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i'))) \<and>
      r_que_aux ((locals_' x)!i') (port_channel conf (communication_' x) (pt ((locals_' x)!i')))  = 
      r_que_aux ((locals_' x')!i') (port_channel conf (communication_' x') (pt ((locals_' x)!i'))) 
  "
unfolding preserves_locals_constr'_def by fastforce

lemma preserv_locals_sim'_a1: 
  "(x,x',i) \<in> preserves_locals_constr' \<Longrightarrow>
   (x',x,i) \<in> preserves_locals_constr'"
proof -
  assume a0:"(x,x',i) \<in> preserves_locals_constr'"       
  thus ?thesis unfolding preserves_locals_constr'_def 
  apply auto by metis+
qed

lemma preserv_locals_sim': 
     "(x,x',i) \<in> preserves_locals_constr' \<longleftrightarrow>
      (x',x,i) \<in> preserves_locals_constr'"
using preserv_locals_sim'_a1 by metis

lemma preserves_locals_D1:
  "(x,x',i)\<in> preserves_locals_constr \<Longrightarrow> 
    length (locals_' x) =  length (locals_' x')
  "
 unfolding preserves_locals_constr_def by auto

lemma preserves_locals_D2:
  "(x,x',i)\<in> preserves_locals_constr \<Longrightarrow> 
     \<forall>i'. (i\<noteq>i' \<longrightarrow> evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                    pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                    
                    a_que_aux ((locals_' x)!i')  = 
                    a_que_aux ((locals_' x')!i') \<and>
                    r_que_aux ((locals_' x)!i')  = 
                    r_que_aux ((locals_' x')!i') )
  "
unfolding preserves_locals_constr_def by fastforce

lemma preserves_locals_D3:
  "(x,x',i)\<in> preserves_locals_constr \<Longrightarrow> 
     evnt ((locals_' x)!i) = evnt ((locals_' x')!i) \<and>
     pt ((locals_' x)!i) = pt ((locals_' x')!i) 
  "
unfolding preserves_locals_constr_def by auto

lemma preserv_locals_sim_a1: 
  "(x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
   (x',x,i) \<in> preserves_locals_constr"
proof -
  assume a0:"(x,x',i) \<in> preserves_locals_constr"  
  then have a1:"length (locals_' x) =  length (locals_' x') \<and>
             (\<forall>i'. (i\<noteq>i' \<longrightarrow>  evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                               pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                               
                               a_que_aux ((locals_' x)!i')  = 
                                a_que_aux ((locals_' x')!i') \<and>
                                r_que_aux ((locals_' x)!i')  = 
                               r_que_aux ((locals_' x')!i')) \<and>
                   (i=i' \<longrightarrow> evnt ((locals_' x)!i) = evnt ((locals_' x')!i) \<and>
                                pt ((locals_' x)!i) = pt ((locals_' x')!i)))
                               "
  unfolding preserves_locals_constr_def by fastforce
  then have l:"length (locals_' x') =  length (locals_' x)" by auto
  have "(\<forall>i'. (i\<noteq>i' \<longrightarrow>  evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                         pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                         
                         a_que_aux ((locals_' x)!i')  = 
                          a_que_aux ((locals_' x')!i') \<and>
                          r_que_aux ((locals_' x)!i')  = 
                          r_que_aux ((locals_' x')!i') ) \<and>
               (i=i' \<longrightarrow> evnt ((locals_' x')!i) = evnt ((locals_' x)!i) \<and>
                         pt ((locals_' x')!i) = pt ((locals_' x)!i)))"
  using a1 by fastforce 
  thus ?thesis using l unfolding preserves_locals_constr_def by auto
qed

lemma aux_eq: "(x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
               (a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
               (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i)) \<Longrightarrow>
               \<forall>i. (a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
                   (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i))"
using preserves_locals_D2 by fastforce

lemma preserv_locals_sim: 
     "(x,x',i) \<in> preserves_locals_constr \<longleftrightarrow>
      (x',x,i) \<in> preserves_locals_constr"
using preserv_locals_sim_a1 by metis

definition preserves_comm_constr
where
"preserves_comm_constr  \<equiv> 
   {(x,x',ch). (\<forall>ch'. ch\<noteq>ch' \<longrightarrow> (chans (communication_' x) ch') = 
                                  (chans (communication_' x') ch')) \<and>
                ports (communication_' x) = ports (communication_' x')}
"

lemma preserv_comm_sim_a1: 
    "(x,x',ch) \<in> preserves_comm_constr \<Longrightarrow>
     (x',x,ch) \<in> preserves_comm_constr"
proof -
  {
   assume a0:"(x,x',ch) \<in> preserves_comm_constr" 
   then have channels:
   "(\<forall>ch'. (ch\<noteq>ch'\<longrightarrow> (chans (communication_' x)) ch' =  (chans (communication_' x')) ch')) \<and>
           ports (communication_' x) = ports (communication_' x')"
     using a0 unfolding preserves_comm_constr_def by auto  
    then show "(x',x,ch) \<in> preserves_comm_constr"
    unfolding preserves_comm_constr_def by fastforce    
  }
qed

lemma preserv_comm_sim:
   "(x',x,ch) \<in> preserves_comm_constr \<longleftrightarrow>
    (x,x',ch) \<in> preserves_comm_constr"
using preserv_comm_sim_a1
by metis 

lemma preserves_comm_D2:"
       (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>
       \<forall>ch_id'. ch_id\<noteq>ch_id' \<longrightarrow> (chans (communication_' x)) ch_id' =  
                                 (chans (communication_' x')) ch_id'"
unfolding preserves_comm_constr_def
by auto

lemma preserves_comm_D3:"
       (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>
       ports (communication_' x) = ports (communication_' x')"
unfolding preserves_comm_constr_def
by auto

text{* lemmas on modifying the auxiliar set of messages*}



lemma channel_messages_eq:
     "
     (x1,y1,i) \<in> preserves_locals_constr  \<Longrightarrow>
    a_que_aux ((locals_' x1)!i) ch  = a_que_aux ((locals_' y1)!i) ch \<and>
    r_que_aux ((locals_' x1)!i) ch  = r_que_aux ((locals_' y1)!i) ch \<Longrightarrow>
     (channel_messages  ch a_que_aux (locals_' x1)) = 
       (channel_messages  ch a_que_aux (locals_' y1)) \<and>
       (channel_messages  ch r_que_aux (locals_' x1)) = 
       (channel_messages  ch r_que_aux (locals_' y1))"
proof-
  assume 
         a1: "(x1,y1,i) \<in> preserves_locals_constr" and
         a2: "(a_que_aux ((locals_' x1)!i) ch  = 
              a_que_aux ((locals_' y1)!i) ch) \<and>
              (r_que_aux ((locals_' x1)!i) ch  = 
              r_que_aux ((locals_' y1)!i) ch)"
  then have "\<forall>i'. i\<noteq>i' \<longrightarrow>  evnt ((locals_' x1)!i') = evnt ((locals_' y1)!i') \<and>
                             pt ((locals_' x1)!i') = pt ((locals_' y1)!i') \<and>                             
                             a_que_aux ((locals_' x1)!i') ch = 
                             a_que_aux ((locals_' y1)!i') ch \<and>
                             r_que_aux ((locals_' x1)!i') ch  = 
                             r_que_aux ((locals_' y1)!i') ch"
    using preserves_locals_D2 by auto
  moreover have "pt ((locals_' x1)!i) = pt ((locals_' y1)!i)" 
    using a1 preserves_locals_D3 by auto  
  moreover have "evnt ((locals_' x1) ! i) = evnt ((locals_' y1)  ! i)"
    using preserves_locals_D3 a1 by auto
 
  ultimately have "(\<forall>i'<length (locals_' x1).
                  evnt ((locals_' x1) ! i') = evnt ((locals_' y1)  ! i') \<and>
                  a_que_aux ((locals_' x1)!i') ch = 
                 a_que_aux ((locals_' y1)!i') ch \<and>
                 r_que_aux ((locals_' x1)!i') ch = 
                 r_que_aux ((locals_' y1)!i') ch \<and> 
                  pt ((locals_' x1) ! i') = pt ((locals_' y1)  ! i'))"
  using a2  by auto  
  also have "length (locals_' x1) = length (locals_' y1)" using preserves_locals_D1 a1 by auto 
  ultimately show ?thesis using   preserves_locals_D1
    by (simp add: same_channel_messages) 
qed

  
  lemma channel_messages_eq':
     "(x1,y1,i) \<in> preserves_locals_constr'  \<Longrightarrow>   
      (port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) =
      (port_channel conf (communication_' y1) (pt ((locals_' x1)!i))) \<Longrightarrow>
     (channel_messages  (port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) a_que_aux (locals_' x1)) = 
       (channel_messages  (port_channel conf  (communication_' y1) (pt ((locals_' x1)!i))) a_que_aux (locals_' y1)) \<and>
       (channel_messages  (port_channel conf  (communication_' x1)  (pt ((locals_' x1)!i))) r_que_aux (locals_' x1)) = 
       (channel_messages  (port_channel conf  (communication_' y1) (pt ((locals_' x1)!i))) r_que_aux (locals_' y1))"
proof-
  assume 
         a1: "(x1,y1,i) \<in> preserves_locals_constr'"   and
         a1':"(port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) =
              (port_channel conf (communication_' y1) (pt ((locals_' x1)!i)))"
         
  have a2:"\<forall>i'.  evnt ((locals_' x1)!i') = evnt ((locals_' y1)!i') \<and>
                   pt ((locals_' x1)!i') = pt ((locals_' y1)!i') \<and>                             
                   a_que_aux ((locals_' x1)!i')  (port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) = 
                   a_que_aux ((locals_' y1)!i')  (port_channel conf (communication_' y1) (pt ((locals_' x1)!i))) \<and>
                   r_que_aux ((locals_' x1)!i') (port_channel conf (communication_' x1) (pt ((locals_' x1)!i)))  = 
                   r_que_aux ((locals_' y1)!i') (port_channel conf (communication_' y1) (pt ((locals_' x1)!i)))"
    using a1 preserves_locals'_D2 by auto
  moreover have "pt ((locals_' x1)!i) = pt ((locals_' y1)!i)" 
    using a1 unfolding preserves_locals_constr'_def by auto  
  moreover have "evnt ((locals_' x1) ! i) = evnt ((locals_' y1)  ! i)"
    using  a1 unfolding preserves_locals_constr'_def by auto
 
  ultimately have "(\<forall>i'<length (locals_' x1).
                  evnt ((locals_' x1) ! i') = evnt ((locals_' y1)  ! i') \<and>
                  a_que_aux ((locals_' x1)!i') (port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) = 
                 a_que_aux ((locals_' y1)!i') (port_channel conf (communication_' y1) (pt ((locals_' x1)!i))) \<and>
                 r_que_aux ((locals_' x1)!i') (port_channel conf (communication_' x1) (pt ((locals_' x1)!i))) = 
                 r_que_aux ((locals_' y1)!i') (port_channel conf(communication_' y1)  (pt ((locals_' x1)!i))) \<and> 
                  pt ((locals_' x1) ! i') = pt ((locals_' y1)  ! i'))"
  using a2  by auto  
  also have "length (locals_' x1) = length (locals_' y1)" using preserves_locals'_D1 a1 by auto 
  ultimately show ?thesis using   preserves_locals'_D1 a1'
    by (simp add: same_channel_messages) 
qed


  
lemma  add_channel_message_evnt:
  " i<length (locals_' x) \<Longrightarrow>           
  (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
  aux_msg ((locals_' x')!i) ch =  aux_msg (locals_' x ! i) ch + mess \<Longrightarrow>  
  aux_msg = a_que_aux \<or> aux_msg = r_que_aux \<Longrightarrow>                             
      channel_messages  ch aux_msg (locals_' x)  + mess  =
              channel_messages  ch aux_msg (locals_' x') 
"
proof -
assume a0:"i<length (locals_' x)" and                             
       a1:  "(x,x',i) \<in> preserves_locals_constr" and
       a2: "aux_msg ((locals_' x')!i) ch =  aux_msg (locals_' x ! i) ch + mess" and
       a3: "aux_msg = a_que_aux \<or> aux_msg = r_que_aux" 
  have other_locals_eq:"\<forall>i'. i'\<noteq>i \<longrightarrow> evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                    pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                    
                    aux_msg ((locals_' x)!i') ch = 
                    aux_msg ((locals_' x')!i') ch"
  using preserves_locals_D2[OF a1] a3  by fastforce    
  then have other_aux_msg_eq:"\<forall>i'. i'\<noteq>i \<longrightarrow>
                    aux_msg ((locals_' x)!i') ch = aux_msg ((locals_' x')!i') ch"
    by auto  
  have len:"length (locals_' x) = length (locals_' x')" using preserves_locals_D1[OF a1] by auto
  have assig: "aux_msg ((locals_' x')!i) ch =  aux_msg (locals_' x ! i) ch  + mess" 
    using a2 by auto
  show ?thesis 
  using  a0 other_aux_msg_eq assig add_message_channel[OF a0 len _, of aux_msg ch mess] by auto  
qed

lemma  add_channel_message_not_evnt:
  "         
  (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>   
  aux_msg = a_que_aux \<or> aux_msg = r_que_aux \<Longrightarrow>
  aux_msg ((locals_' x)!i) ch =  aux_msg ((locals_' x')!i) ch \<Longrightarrow>                                
      channel_messages  ch aux_msg (locals_' x) =
      channel_messages  ch aux_msg (locals_' x')  
"
proof -
assume a0:  " (x,x',i) \<in> preserves_locals_constr" and
       a1: "aux_msg = a_que_aux \<or> aux_msg = r_que_aux" and 
       a2: "aux_msg ((locals_' x)!i) ch =  aux_msg ((locals_' x')!i) ch"            
  have other_locals_eq:"\<forall>i'. i'\<noteq>i \<longrightarrow> evnt ((locals_' x)!i') = evnt ((locals_' x')!i') \<and>
                    pt ((locals_' x)!i') = pt ((locals_' x')!i') \<and>                    
                    aux_msg ((locals_' x)!i') ch = 
                    aux_msg ((locals_' x')!i') ch"
  using preserves_locals_D2[OF a0] a1  by fastforce 
  then have other_aux_msg_eq:"\<forall>i'. i'\<noteq>i \<longrightarrow>
                    aux_msg ((locals_' x)!i') ch = aux_msg ((locals_' x')!i') ch"
    by auto 
  have len:"length (locals_' x) = length (locals_' x')" using preserves_locals_D1[OF a0] by auto
  thus ?thesis using same_message_channel[OF len, of i aux_msg ch] other_aux_msg_eq a2 by auto
qed 

text{* Lemmas on the preservation of ch\_spec and channel\_spec when modifying abstract states 
       it is assumed that locals constrains are not changed*}

text{*not modifying the queue communication nor the auxiliary variable preserves
     ch\_spec and channel\_spec this is the weakest precondition that satisfies
    the relation*}

subsection {* Specification of the Rely Guarantee *}


lemma ch_spec_eq:  
    "chans (communication_' x1) =chans (communication_' y1) \<Longrightarrow>
     (x1,y1,i) \<in> preserves_locals_constr  \<Longrightarrow>
     a_que_aux ((locals_' x1)!i) ch = a_que_aux ((locals_' y1)!i) ch \<Longrightarrow>
     r_que_aux ((locals_' x1)!i) ch = r_que_aux ((locals_' y1)!i) ch \<Longrightarrow>     
     ch_spec B  adds rems ch x1 \<Longrightarrow> ch_spec B  adds rems ch y1"
proof -
  assume a0:"chans (communication_' x1) =chans(communication_' y1)" and
         a1:"(x1,y1,i) \<in> preserves_locals_constr" and
         a2:"a_que_aux ((locals_' x1)!i) ch = a_que_aux ((locals_' y1)!i) ch" and
         a3: "r_que_aux ((locals_' x1)!i) ch = r_que_aux ((locals_' y1)!i) ch" and
         a4:"ch_spec B  adds rems ch x1"
   have 
     eq_channel_message1:
       "channel_messages  ch  a_que_aux (locals_' x1)  = 
         channel_messages  ch a_que_aux (locals_' y1)" and
     eq_channel_message2:
       "channel_messages  ch  r_que_aux (locals_' x1)  = 
         channel_messages  ch r_que_aux (locals_' y1)"
     using channel_messages_eq a0 a1 a2 a3   by auto
    thus ?thesis using a2 a3 a0 a4 unfolding ch_spec_def 
          channel_received_messages_def channel_sent_messages_def
      using a1 preserves_locals_D1 by fastforce
qed

lemma channel_spec_eq:  
    "chans (communication_' x1) =chans(communication_' y1) \<Longrightarrow>
     (x1,y1,i) \<in> preserves_locals_constr  \<Longrightarrow>
     a_que_aux ((locals_' x1)!i)  = a_que_aux ((locals_' y1)!i)  \<Longrightarrow>
     r_que_aux ((locals_' x1)!i)  = r_que_aux ((locals_' y1)!i)  \<Longrightarrow>
     channel_spec B  adds rems ch_id x1 \<Longrightarrow>
     channel_spec B  adds rems ch_id y1"
using ch_spec_eq channel_spec_dest2 channel_spec_intro preserves_locals_D3 by fastforce 


lemma channel_not_queport_full_size:
" state_conf  x \<Longrightarrow>  
  port_open (communication_' x) p_id \<Longrightarrow>
  ch_spec B adds rems ch_id x \<Longrightarrow>    
  \<not> port_full conf (communication_' x) p_id \<Longrightarrow>
  p_queuing conf (communication_' x) p_id \<Longrightarrow>  
  port_in_channel conf (communication_' x) p_id  ch_id \<Longrightarrow>
  (chans (communication_' x) ch_id) = Some ch \<Longrightarrow>
  size (channel_get_messages (channel_insert_message  ch m t) ) \<le>
   channel_size (get_channel conf ch_id) 
 "
proof -
assume
   a0: "ch_spec B adds rems ch_id x" and
   a1: "\<not> port_full conf (communication_' x) p_id " and   
   a1':"port_open (communication_' x) p_id " and
   a2: "p_queuing conf (communication_' x) p_id" and
   a3: "port_in_channel conf (communication_' x) p_id ch_id" and
   a4: "state_conf  x" and   
   a6: "(chans (communication_' x) ch_id) = Some ch"
   have not_channe_full:"\<not> channel_full conf (communication_' x) ch_id"
     using port_not_full_channel_not_full[OF a4 a1' a1 a3]  by auto   
   have "chan_queuing ch" 
     using a6 a2 a3 a4  ch_id_queuing_def option.sel p_queuing_def 
     by (metis a1' p_queuing_chan_queuing)      
   then have " channel_get_bufsize (channel_insert_message ch m t)
                = (channel_get_bufsize ch) + 1"
     using insert_message_inc_buf_size  
     by fastforce
   moreover have "\<not> (channel_size (get_channel conf ch_id)  = 
                      channel_get_bufsize ch)"
     using not_channe_full a6 port_in_channel_get_channel[OF a3]  port_channel
     unfolding channel_full_def
     by fastforce
   moreover have "size (channel_get_messages ch) \<le> 
                   channel_size (get_channel conf ch_id)"
     using Int_Collect a0 a6  unfolding ch_spec_def
     using option.sel order_refl
     using a3 channel_full_def channel_get_bufsize_def not_channe_full port_in_channel_get_channel by fastforce       
   ultimately show ?thesis unfolding channel_get_bufsize_def
     by auto           
 qed 
   
  (* lemma channel_not_queport_empty_size:
" state_conf  x \<Longrightarrow>  
  ch_spec B adds rems ch_id x \<Longrightarrow>      
  p_queuing conf p_id \<Longrightarrow>  
  port_in_channel conf p_id  ch_id \<Longrightarrow>
  (chans (communication_' x) ch_id) = Some ch \<Longrightarrow>
  size (channel_get_messages (channel_remove_message  ch m) ) \<le>
   channel_size (get_channel conf ch_id) 
 "
proof -
assume
   a0: "ch_spec B adds rems ch_id x" and   
   a2: "p_queuing conf p_id" and
   a3: "port_in_channel conf p_id ch_id" and
   a4: "state_conf  x" and   
   a6: "(chans (communication_' x) ch_id) = Some ch"     
   have "chan_queuing ch" 
     using a6 a2 a3 a4 port_channel ch_id_queuing_def option.sel p_queuing_def state_conf_def
     by metis (* by auto *)      
   then have " channel_get_bufsize (channel_remove_message ch m)
                \<le> (channel_get_bufsize ch)"
     using remove_message_less_eq_buf_size  
     by fastforce
   moreover have "size (channel_get_messages ch) \<le> 
                   channel_size (get_channel conf ch_id)"
     using Int_Collect a0 a6  unfolding ch_spec_def
     using option.sel order_refl
     using a3 channel_full_def channel_get_bufsize_def  port_in_channel_get_channel by fastforce       
   ultimately show ?thesis unfolding channel_get_bufsize_def
     by auto           
 qed *)
   
 subsection {* Properties on channel spec*}   
   text {* modifying the mutex preserves ch\_spec*}
lemma local_constr_eq_que_ch_spec:
  "ch_spec B adds rems ch_id x \<Longrightarrow> 
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
    channel_get_messages (the (chans (communication_' x) ch_id)) = 
    channel_get_messages (the (chans (communication_' x') ch_id)) \<Longrightarrow>              
   a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id \<Longrightarrow>
   r_que_aux ((locals_' x)!i) ch_id  = r_que_aux ((locals_' x')!i) ch_id \<Longrightarrow>
   ch_spec B adds rems ch_id x'"
proof - 
  assume a1: "ch_spec B adds rems ch_id x" and 
         a2: "(x,x',i) \<in> preserves_locals_constr" and
         a3: " channel_get_messages (the (chans (communication_' x) ch_id)) = 
               channel_get_messages (the (chans (communication_' x') ch_id))" and       
         a4: "a_que_aux ((locals_' x)!i) ch_id  = a_que_aux ((locals_' x')!i) ch_id" and
         a5: "r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id"
   have " channel_messages  ch_id a_que_aux (locals_' x)  = 
          channel_messages  ch_id a_que_aux (locals_' x') \<and>
          channel_messages  ch_id r_que_aux (locals_' x)  = 
          channel_messages  ch_id r_que_aux (locals_' x')"        
    unfolding preserves_locals_constr_def
    using a2 channel_messages_eq a4 a5 by fastforce
   then show ?thesis using a1 a3 
     unfolding ch_spec_def channel_received_messages_def 
         channel_sent_messages_def Let_def
     using a2 preserves_locals_D1 by fastforce
qed



text {* modifying comm of ch=port\_quechannel (pt ((locals\_' x)!i)) 
       preserving locals const and comm constrains               
        preserves channel\_spec of any channel different from  ch
      this helps to preserve the invariant when adding an element to the queue
     in ch and modifying the aux\_msg proving that the event does not
      modify any ch' != ch*}
(*lemma preserve_locals_comm_ch_spec_not_ch:
  "x\<in> channel_spec B adds rems ch_id \<Longrightarrow> 
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow> 
   (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>  
   \<forall>ch_id'. ch_id \<noteq> ch_id' \<longrightarrow> 
         (a_que_aux ((locals_' x)!i) ch_id' = a_que_aux ((locals_' x')!i) ch_id')  \<and>
         (r_que_aux ((locals_' x)!i) ch_id' = r_que_aux ((locals_' x')!i) ch_id') \<Longrightarrow>           
   \<forall>ch_id' ch. ch_id'\<noteq>ch_id \<longrightarrow> 
      ((chans (communication_' x') ch_id') = Some ch \<and> 
        ch_id_queuing conf ch_id' \<and> channel_get_mutex ch = 0 \<longrightarrow>
         ch_spec B adds rems ch_id' x')"
proof-
  assume
  
  a1: "x\<in> channel_spec B adds rems ch_id" and 
  a2: "(x,x',i) \<in> preserves_locals_constr" and        
  a3: "(x,x',ch_id)\<in> preserves_comm_constr" and 
  a4: "\<forall>ch_id'. ch_id \<noteq> ch_id' \<longrightarrow> 
         (a_que_aux ((locals_' x)!i) ch_id' = a_que_aux ((locals_' x')!i) ch_id')  \<and>
         (r_que_aux ((locals_' x)!i) ch_id' = r_que_aux ((locals_' x')!i) ch_id')"   
  {fix ch_id' ch'   
   assume ass0:"ch_id'\<noteq>ch_id" and
          ass1:"channel_get_mutex ch' = 0 \<and> ch_id_queuing conf ch_id' \<and>
                (chans (communication_' x') ch_id') = Some ch'"  
   then have eq_chans:
      "(chans (communication_' x) ch_id') =
       (chans (communication_' x') ch_id')"  
     using preserves_comm_D2[OF a3] by auto  
   then have "channel_get_mutex ch' = 0 \<and> ch_id_queuing conf ch_id' \<and>
              (chans (communication_' x) ch_id') = Some ch'"
     using ass1 by auto   
   then have ch:"ch_spec B adds rems ch_id' x"  
     using a1 unfolding channel_spec_def ch_spec_def Let_def
     by fastforce    
   then have "ch_spec B  adds rems ch_id' x'" 
     using local_constr_eq_que_ch_spec[OF ch a2 ] eq_chans a4 ass0
     by auto
  } 
  thus ?thesis by auto
qed
  *)

text {*setting the mutex with a value different than zero 
       preserves channel\_spec*}



text {* modifying the mutex to any value and preserving comm\_constr for the enviroment
        (channel different than ch is not modified) satisfies  channel\_spec if ch\_spec*}
lemma local_constr_ch_spec_channel_spec:
  "
   channel_spec B adds rems ch_id x \<Longrightarrow>     
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
    channel_get_messages (the (chans (communication_' x) ch_id)) = 
    channel_get_messages (the (chans (communication_' x') ch_id)) \<Longrightarrow>       
   (a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
   (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i)) \<Longrightarrow>
  \<exists>ch. chans (communication_' x) ch_id = Some ch \<Longrightarrow>
    channel_spec B adds rems ch_id x'"
proof -  
  assume 
         a1: "channel_spec B adds rems ch_id x" and 
         a2: "(x,x',i) \<in> preserves_locals_constr" and
         a3: "channel_get_messages (the (chans (communication_' x) ch_id)) = 
              channel_get_messages (the (chans (communication_' x') ch_id))" and        
         a5: "\<exists>ch. chans (communication_' x) ch_id = Some ch" and
         a6: "(a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
              (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i))" 
  {fix ch'
   assume ass:"ch_id_queuing conf ch_id \<and> 
               (chans (communication_' x') ch_id) = Some ch'"  
   then have ch_x:"ch_spec B adds rems ch_id x" 
     using a5 a1 unfolding channel_spec_def by auto
   have "ch_spec B adds rems ch_id x'"
     using local_constr_eq_que_ch_spec[OF ch_x a2 a3] a6 a2 preserves_locals_D3 by force 
  } thus ?thesis  using a2 preserves_locals_D3 unfolding channel_spec_def ch_spec_def by fastforce
qed
  
  lemma local_constr_subset_aux1:
  "
   x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id r_que_aux \<acute>locals \<and>
        channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id a_que_aux \<acute>locals\<rbrace> \<Longrightarrow>     
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
   (a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
   (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id) \<Longrightarrow>  
    channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq>#
        channel_messages ch_id r_que_aux (locals_' x')"
proof -  
  assume 
         a1: "x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id r_que_aux \<acute>locals \<and>
                  channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id a_que_aux \<acute>locals\<rbrace>" and 
         a2: "(x,x',i) \<in> preserves_locals_constr" and         
         a6: "(a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
              (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id)" 
  then show ?thesis
    by (simp add: add_channel_message_not_evnt preserves_locals_D1 preserves_locals_D3)
qed
  
  lemma local_constr_subset_aux2:
  "
   x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id r_que_aux \<acute>locals \<and>
        channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id a_que_aux \<acute>locals\<rbrace> \<Longrightarrow>     
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
   (a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
   (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id) \<Longrightarrow>  
    channel_messages ch_id adds [0..<length (locals_' x')] \<subseteq>#
        channel_messages ch_id a_que_aux (locals_' x')"
proof -  
  assume 
         a1: "x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id r_que_aux \<acute>locals \<and>
                  channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id a_que_aux \<acute>locals\<rbrace>" and 
         a2: "(x,x',i) \<in> preserves_locals_constr" and         
         a6: "(a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
              (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id)" 
  then show ?thesis
    by (simp add: add_channel_message_not_evnt preserves_locals_D1 preserves_locals_D3)
qed
  
lemma local_constr_subset_aux:
  "
   x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id r_que_aux \<acute>locals \<and>
        channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id a_que_aux \<acute>locals\<rbrace> \<Longrightarrow>     
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>
   (a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
   (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id) \<Longrightarrow>  
    x'\<in> \<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id r_que_aux \<acute>locals \<and>
        channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
        channel_messages ch_id a_que_aux \<acute>locals\<rbrace>"
proof -  
  assume 
         a1: "x\<in>\<lbrace>channel_messages ch_id rems [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id r_que_aux \<acute>locals \<and>
                  channel_messages ch_id adds [0..<length \<acute>locals] \<subseteq>#
                  channel_messages ch_id a_que_aux \<acute>locals\<rbrace>" and 
         a2: "(x,x',i) \<in> preserves_locals_constr" and         
         a6: "(a_que_aux ((locals_' x)!i) ch_id = a_que_aux ((locals_' x')!i) ch_id) \<and>
              (r_que_aux ((locals_' x)!i) ch_id = r_que_aux ((locals_' x')!i) ch_id)" 
  then show ?thesis
    by (simp add: add_channel_message_not_evnt preserves_locals_D1 preserves_locals_D3)
qed

text {* modifying the queue when the mutex is not zero preserves channel\_spec*}
lemma "c \<subseteq># (a+(b-d)) \<Longrightarrow> d\<subseteq># b  \<Longrightarrow> add_mset m (a + (b-d) - c) = a + ((add_mset m b)-d) -c "  
  by (metis add_mset_add_single mset_subset_eq_multiset_union_diff_commute union_mset_add_mset_right)

  
lemma atomic_tran_channel_ch_spec:
  "i< length (locals_' x) \<Longrightarrow> 
   state_conf x \<Longrightarrow>   
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>   
   channel_get_messages (the (chans (communication_' x) ch_id)) + {# m #} = 
     channel_get_messages (the (chans (communication_' x') ch_id)) \<Longrightarrow>   
   a_que_aux ((locals_' x')!i) ch_id = a_que_aux ((locals_' x)!i) ch_id + {#m#} \<Longrightarrow>   
   r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i) \<Longrightarrow>   
   (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>   
    port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id \<Longrightarrow>  
    port_open (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    p_queuing conf (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    ch_spec B adds rems ch_id x \<Longrightarrow>
   \<not> port_full conf (communication_' x) (pt(locals_' x!i)) \<Longrightarrow>
    channel_messages ch_id adds [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id a_que_aux (locals_' x) \<Longrightarrow>
   (channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)])
   \<Longrightarrow>
   ch_spec B adds rems ch_id x'"
proof-        
 assume
   a0:"i< length (locals_' x)" and  
   a0':"state_conf x" and
   a2:"(x,x',i) \<in> preserves_locals_constr" and  
   a3:"channel_get_messages (the (chans (communication_' x) ch_id)) + {# m #} = 
       channel_get_messages (the (chans (communication_' x') ch_id))" and
   a4:"a_que_aux ((locals_' x')!i) ch_id = a_que_aux ((locals_' x)!i) ch_id + {#m#}" and   
   a6:"r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i)" and   
   a7:"(x,x',ch_id)\<in> preserves_comm_constr" and
   a8:"port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id " and  
   a8':"port_open (communication_' x) (pt (locals_' x ! i))" and
   a9:"p_queuing conf (communication_' x) (pt (locals_' x ! i))" and
   a10: "ch_spec B adds rems ch_id x" and
   a11:"\<not> port_full conf (communication_' x) (pt(locals_' x!i))" and
   a12:" channel_messages ch_id adds [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id a_que_aux (locals_' x)" and 
   a13:"(channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)])"
  have send_aux:"channel_messages  ch_id a_que_aux (locals_' x)  + {#m#}  = 
                 channel_messages ch_id a_que_aux (locals_' x')"  
    using add_channel_message_evnt[OF a0 a2] a4 by metis
  moreover have rec_aux:"channel_messages  ch_id r_que_aux (locals_' x) = 
                          channel_messages ch_id r_que_aux (locals_' x')"
    using add_channel_message_not_evnt[OF a2 _] a6  by fastforce
  moreover have x:"channel_messages ch_id rems [0..<length (locals_' x)] = channel_messages ch_id rems [0..<length (locals_' x')] \<and> 
                channel_messages ch_id adds [0..<length (locals_' x)] = channel_messages ch_id adds [0..<length (locals_' x')]"
    using a2 preserves_locals_D1 by fastforce   
  ultimately have "channel_get_messages (the (chans (communication_' x') ch_id)) = 
            (B ch_id + channel_sent_messages  ch_id adds (locals_' x')) -
                (channel_received_messages  ch_id rems (locals_' x'))"
    using a10 a3 a4 a3 a12  a13 unfolding channel_received_messages_def ch_spec_def
                channel_sent_messages_def multi_self_add_other_not_self  Let_def
    by (metis (no_types, lifting) add.assoc subset_mset.add_diff_assoc2)                                               
     
  moreover have 
    "channel_messages ch_id r_que_aux (locals_' x') - channel_messages ch_id rems [0..<length (locals_' x')]  
      \<subseteq># B ch_id + (channel_messages ch_id a_que_aux (locals_' x') - channel_messages ch_id adds [0..<length (locals_' x')])"
   using a10 a3 send_aux rec_aux a12 a13
    unfolding ch_spec_def channel_received_messages_def 
              channel_sent_messages_def  Let_def
    by (metis (no_types) a12 a13 ab_semigroup_add_class.add_ac(1) empty_le mset_subset_eq_multiset_union_diff_commute 
                         rec_aux send_aux subset_mset.add_increasing2 x)  
  moreover have 
   "size (channel_get_messages (the (chans (communication_' x') ch_id))) \<le> 
    channel_size (get_channel conf ch_id)"
   using a10 a3 a11 
    unfolding ch_spec_def
    by (metis a0' a10 a8 a8' a9 channel_not_queport_full_size option.sel 
            p_queuing_chan_queuing queuing_insert_message)              
    
  ultimately show ?thesis 
    unfolding ch_spec_def Let_def channel_received_messages_def channel_sent_messages_def
    by (metis a10 ch_spec_def local.x rec_aux send_aux subset_mset.add_increasing2 subset_mset.zero_le)     
qed  
  
lemma "r - ri \<subseteq># B + (s - si) \<Longrightarrow>
       s = s' \<Longrightarrow> r' = r - m \<Longrightarrow> m \<subseteq># B + (s - si) - (r - ri) \<Longrightarrow>
       r' - ri \<subseteq># B + (s' - si)
    "
  by (meson diff_subset_eq_self subset_eq_diff_conv subset_mset.order.trans)  
  
lemma atomic_tran_rem_channel_ch_spec:
  "i< length (locals_' x) \<Longrightarrow> 
   state_conf x \<Longrightarrow>   
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>      
   m \<subseteq># channel_get_messages (the (chans (communication_' x) ch_id)) \<Longrightarrow>
   channel_get_messages (the (chans (communication_' x) ch_id)) - m = 
     channel_get_messages (the (chans (communication_' x') ch_id)) \<Longrightarrow>   
   r_que_aux ((locals_' x')!i) ch_id = r_que_aux ((locals_' x)!i) ch_id + m \<Longrightarrow>   
   a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i) \<Longrightarrow>   
   (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>   
    port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id \<Longrightarrow>    
    p_queuing conf (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    port_open (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    ch_spec B adds rems ch_id x \<Longrightarrow>
   channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id r_que_aux (locals_' x) \<Longrightarrow>
   (channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)])
   \<Longrightarrow>
   ch_spec B adds rems ch_id x'"
proof-        
 assume
   a0:"i< length (locals_' x)" and  
   a0':"state_conf x" and
   a2:"(x,x',i) \<in> preserves_locals_constr" and 
   a3':"m \<subseteq># channel_get_messages (the (chans (communication_' x) ch_id))" and
   a3:"channel_get_messages (the (chans (communication_' x) ch_id)) - m = 
       channel_get_messages (the (chans (communication_' x') ch_id))" and
   a4:"r_que_aux ((locals_' x')!i) ch_id = r_que_aux ((locals_' x)!i) ch_id + m" and   
   a6:"a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)" and   
   a7:"(x,x',ch_id)\<in> preserves_comm_constr" and
   a8:"port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id " and  
   a8':"port_open (communication_' x) (pt (locals_' x ! i))" and
   a9:"p_queuing conf (communication_' x) (pt (locals_' x ! i))" and
   a10: "ch_spec B adds rems ch_id x" and 
   a12':" channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id r_que_aux (locals_' x)" and
   a13:"(channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)])"
  have send_aux:"channel_messages  ch_id r_que_aux (locals_' x)  + m  = 
                 channel_messages ch_id r_que_aux (locals_' x')"  
    using add_channel_message_evnt[OF a0 a2] a4 by metis
  moreover have rec_aux:"channel_messages  ch_id a_que_aux (locals_' x) = 
                          channel_messages ch_id a_que_aux (locals_' x')"
    using add_channel_message_not_evnt[OF a2 _] a6  by fastforce
  moreover have x:"channel_messages ch_id rems [0..<length (locals_' x)] = channel_messages ch_id rems [0..<length (locals_' x')] \<and> 
                channel_messages ch_id adds [0..<length (locals_' x)] = channel_messages ch_id adds [0..<length (locals_' x')]"
    using a2 preserves_locals_D1 by fastforce   
  ultimately have "channel_get_messages (the (chans (communication_' x') ch_id)) = 
            (B ch_id + channel_sent_messages  ch_id adds (locals_' x')) -
                (channel_received_messages  ch_id rems (locals_' x'))"
    using a10 a3 a4 a3  a12' a13 unfolding channel_received_messages_def ch_spec_def
                channel_sent_messages_def multi_self_add_other_not_self  Let_def
    by (metis (no_types, hide_lams) diff_diff_add_mset subset_mset.add_diff_assoc2)    
  moreover have 
    "channel_messages ch_id r_que_aux (locals_' x') - channel_messages ch_id rems [0..<length (locals_' x')]  
      \<subseteq># B ch_id + (channel_messages ch_id a_que_aux (locals_' x') - channel_messages ch_id adds [0..<length (locals_' x')])"
   using a10 a3 send_aux rec_aux  a12' a13 a3'
    unfolding ch_spec_def channel_received_messages_def 
              channel_sent_messages_def  Let_def x
    by (metis add_msg_rec x)     
  moreover have 
   "size (channel_get_messages (the (chans (communication_' x') ch_id))) \<le> 
    channel_size (get_channel conf ch_id)"
   using a10 a3  a0' a10 a8 a9 a3'
   unfolding ch_spec_def Let_def
   using size_Diff_submset by fastforce       
  ultimately show ?thesis 
    unfolding ch_spec_def Let_def channel_received_messages_def channel_sent_messages_def
    by (metis a10 ch_spec_def local.x rec_aux send_aux subset_mset.add_increasing2 subset_mset.zero_le)     
qed  



text {* modifying the queue when the mutex is not zero preserves channel\_spec*}


lemma modify_que_channel_ch_spec1:
  " state_conf x \<Longrightarrow>
   ch_spec B adds rems ch_id x \<Longrightarrow> 
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow> 
    chans (communication_' x) ch_id = Some ch \<Longrightarrow>    
    chans (communication_' x') ch_id = Some ch' \<Longrightarrow>
   channel_get_messages ch + {# msg ((locals_' x')!i) #} =  
   channel_get_messages ch' \<Longrightarrow>
   (a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
   (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i)) \<Longrightarrow>   
    port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id \<Longrightarrow>
   port_open (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    \<not> port_full conf  (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>
    p_queuing conf  (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>   
   (channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)]) \<Longrightarrow>
    channel_get_messages  ch' = 
      (B ch_id + channel_sent_messages  ch_id  adds (locals_' x')) - 
                channel_received_messages  ch_id rems (locals_' x')
                + {# msg ((locals_' x')!i) #} \<and>
      channel_received_messages  ch_id rems (locals_' x')  \<subseteq>#
        B ch_id + channel_sent_messages  ch_id adds (locals_' x') \<and>
      size (channel_get_messages ch') \<le> 
         channel_size (get_channel conf ch_id)"
proof-        
 assume 
  
   a0':"state_conf x" and
   a1:"ch_spec B adds rems ch_id x" and
   a2:"(x,x',i) \<in> preserves_locals_constr" and 
   a3:" chans (communication_' x) ch_id = Some ch" and
   a4:" chans (communication_' x') ch_id = Some ch'" and
   a5:"channel_get_messages ch + {# msg ((locals_' x')!i) #} =  
       channel_get_messages ch'" and
   a6: "(a_que_aux ((locals_' x)!i) = a_que_aux ((locals_' x')!i)) \<and>
        (r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i))" and  
   a7:" port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id " and
   a8:"\<not> port_full conf (communication_' x) (pt (locals_' x ! i))" and
   a8':"port_open (communication_' x) (pt (locals_' x !i))" and
   a9:"p_queuing conf (communication_' x) (pt (locals_' x ! i))" and   
   a10:"(channel_messages ch_id r_que_aux (locals_' x) - channel_messages ch_id rems [0..<length (locals_' x)]) \<subseteq>#
    B ch_id + (channel_messages ch_id a_que_aux (locals_' x) - channel_messages ch_id adds [0..<length (locals_' x)])" 
   
  also have len_locals:"length (locals_' x) = length (locals_' x')" 
    using a2 preserves_locals_D1 by fastforce
  ultimately have ev:"(channel_messages  ch_id a_que_aux (locals_' x)) = 
              (channel_messages  ch_id a_que_aux (locals_' x')) \<and>
              (channel_messages  ch_id r_que_aux (locals_' x)) = 
              (channel_messages  ch_id r_que_aux (locals_' x'))"
   using channel_messages_eq by fastforce
 then have "channel_get_messages ch' = 
      (B ch_id + channel_sent_messages ch_id adds  (locals_' x')) -
       channel_received_messages  ch_id  rems(locals_' x') + {# msg ((locals_' x')!i) #}"
   using   a1 a3  a5 len_locals
   unfolding ch_spec_def  
             channel_received_messages_def channel_sent_messages_def
   by simp             
 moreover have "channel_received_messages  ch_id rems (locals_' x') \<subseteq>#
                 B ch_id + channel_sent_messages ch_id adds (locals_' x')"
   using ev a1 a3 a10 len_locals
   unfolding channel_received_messages_def  
              channel_sent_messages_def ch_spec_def 
   by auto
 moreover have "(size (channel_get_messages ch') \<le> 
                  channel_size (get_channel conf ch_id))"
  proof -
    have ch_q:"chan_queuing ch" 
      using p_queuing_chan_queuing[OF a0' a8' a9 a7] a3 by auto
    show ?thesis using queuing_insert_message[OF ch_q]
      using channel_not_queport_full_size[OF a0' a8' a1 a8 a9 a7 a3] a5
      by metis
  qed
 ultimately show ?thesis by auto
qed

lemma modify_que_channel_ch_spec:
  "i< length (locals_' x) \<Longrightarrow> 
   state_conf x \<Longrightarrow>   
   (x,x',i) \<in> preserves_locals_constr \<Longrightarrow>   
   channel_get_messages (the (chans (communication_' x) ch_id)) = 
     channel_get_messages (the (chans (communication_' x') ch_id)) \<Longrightarrow>   
   a_que_aux ((locals_' x')!i) ch_id = a_que_aux ((locals_' x)!i) ch_id + {#m#} \<Longrightarrow>   
   r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i) \<Longrightarrow>   
   (x,x',ch_id)\<in> preserves_comm_constr \<Longrightarrow>   
    port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id \<Longrightarrow>   
    port_open (communication_' x) (pt ((locals_' x)!i)) \<Longrightarrow>
    p_queuing conf (communication_' x) (pt (locals_' x ! i)) \<Longrightarrow>    
     channel_get_messages (the (chans (communication_' x) ch_id)) = 
            (B ch_id + channel_sent_messages ch_id adds (locals_' x)) -
                 channel_received_messages ch_id rems (locals_' x) +  {#m#} \<and>
             channel_received_messages ch_id  rems (locals_' x)  \<subseteq>#
             (B ch_id + channel_sent_messages  ch_id  adds (locals_' x)) \<and>
          (size (channel_get_messages (the (chans (communication_' x) ch_id))) \<le> 
             channel_size (get_channel conf ch_id)) \<and>
     channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id r_que_aux (locals_' x) \<and>
    channel_messages ch_id adds [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id a_que_aux (locals_' x) \<Longrightarrow>
   ch_spec B adds rems ch_id x'"
proof-        
 assume 
   a0:"i< length (locals_' x)" and  
   a0':"state_conf x" and
   a2:"(x,x',i) \<in> preserves_locals_constr" and  
   a3:"channel_get_messages (the (chans (communication_' x) ch_id)) = 
         channel_get_messages (the (chans (communication_' x') ch_id))" and
   a4:"a_que_aux ((locals_' x')!i) ch_id = a_que_aux ((locals_' x)!i) ch_id + {#m#}" and   
   a6:"r_que_aux ((locals_' x)!i) = r_que_aux ((locals_' x')!i)" and   
   a7:"(x,x',ch_id)\<in> preserves_comm_constr" and
   a8:"port_in_channel conf (communication_' x) (pt ((locals_' x)!i)) ch_id " and   
   a8':"port_open (communication_' x) (pt ((locals_' x)!i))" and
   a9:"p_queuing conf (communication_' x) (pt (locals_' x ! i))" and
   a10: "channel_get_messages (the (chans (communication_' x) ch_id)) = 
            (B ch_id + channel_sent_messages ch_id adds  (locals_' x)) -
                channel_received_messages ch_id  rems (locals_' x) + {#m#} \<and>
          channel_received_messages  ch_id  rems (locals_' x) \<subseteq>#
             (B ch_id + channel_sent_messages ch_id adds (locals_' x)) \<and>
          (size (channel_get_messages (the (chans (communication_' x) ch_id))) \<le> 
             channel_size (get_channel conf ch_id)) \<and>
        channel_messages ch_id rems [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id r_que_aux (locals_' x) \<and>
        channel_messages ch_id adds [0..<length (locals_' x)] \<subseteq># channel_messages  ch_id a_que_aux (locals_' x)"
  then have len_loc:"length (locals_' x) = length (locals_' x')"
    using preserves_locals_D1 by blast
  have send_aux:"channel_messages  ch_id a_que_aux (locals_' x)  + {#m#}  = 
                       channel_messages ch_id a_que_aux (locals_' x')"  
    using add_channel_message_evnt[OF a0 a2] a4 by metis
  moreover have rec_aux:"channel_messages  ch_id r_que_aux (locals_' x) = 
                          channel_messages ch_id r_que_aux (locals_' x')"
    using add_channel_message_not_evnt[OF a2 _] a6  by fastforce
  ultimately have "channel_get_messages (the (chans (communication_' x') ch_id)) = 
            (B ch_id + channel_sent_messages  ch_id adds (locals_' x')) -
                (channel_received_messages  ch_id rems (locals_' x')) \<and>
             channel_received_messages  ch_id rems (locals_' x') \<subseteq># 
                   (B ch_id + channel_sent_messages ch_id adds  (locals_' x'))"
    using len_loc a10 a3
  proof -
    have f1: "\<forall>m ma mb. \<not> (m::Message multiset) \<subseteq># ma \<or> ma - m + mb = ma + mb - m"
      by (metis subset_mset.add_diff_assoc2)
    have "channel_sent_messages ch_id adds (locals_' x') =
           channel_messages ch_id a_que_aux (locals_' x) + {#m#} - 
           channel_messages ch_id adds [0..<length (locals_' x)]"
      using channel_sent_messages_def len_loc send_aux by fastforce
    then have "channel_sent_messages ch_id adds (locals_' x') = 
                channel_messages ch_id a_que_aux (locals_' x) - 
                channel_messages ch_id adds [0..<length (locals_' x)] + {#m#}"
      using f1 a10 by presburger
    then have f2: "B ch_id + channel_sent_messages ch_id adds (locals_' x') = 
                   B ch_id + channel_sent_messages ch_id adds (locals_' x) + {#m#}"
      by (simp add: channel_sent_messages_def)
    have "channel_received_messages ch_id rems (locals_' x') = 
          channel_received_messages ch_id rems (locals_' x)"
      using channel_received_messages_def len_loc rec_aux by presburger
    then show ?thesis
      using f2 f1 a10 a3
      by (metis mset_subset_eq_add_left subset_mset.add_increasing2 
                subset_mset.le_add_same_cancel1) 
  qed                                                     
  then show ?thesis 
    using a10 a3 send_aux rec_aux 
    unfolding ch_spec_def channel_received_messages_def 
              channel_sent_messages_def  Let_def
    by (metis len_loc mset_subset_eq_add_left subset_mset.order_trans)    
qed
  
   
section {* Rely Guarantee Specification*}   

(*definition "Guarantee_aux"
  where
    "Guarantee_aux adds B rems x y \<equiv>
  \<forall>ch_id j.
       (mut (the (chans (communication_' x) ch_id)) = j+1 \<and> 
       mut (the (chans (communication_' y) ch_id)) = 0 )  \<longrightarrow>
      (port_channel conf (pt (locals_' x !j))) = ch_id \<and> j<length (locals_' x) \<and> 
      ((r_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j)))\<noteq>rems j (port_channel conf (pt (locals_' x !j))) \<longrightarrow>
       (\<exists>m. r_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j))) = 
          rems j (port_channel conf (pt (locals_' x !j))) + m \<and>
        m\<subseteq># B (port_channel conf (pt (locals_' x !j))) + channel_sent_messages  (port_channel conf (pt (locals_' y !j))) adds  (locals_' x)) \<and>
     a_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j))) = adds j (port_channel conf (pt (locals_' x !j)))
     ) \<and>
     (a_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j)))\<noteq>adds j (port_channel conf (pt (locals_' x !j))) \<longrightarrow>
       a_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j))) = {#msg (locals_' x !j)#} + adds j  (port_channel conf (pt (locals_' x !j))) \<and>
       r_que_aux (locals_' y !j) (port_channel conf (pt (locals_' x !j))) = rems j (port_channel conf (pt (locals_' x !j))) \<and>
       size (channel_get_messages (the (chans (communication_' y) (port_channel conf (pt (locals_' x !j)))))) \<le> 
       channel_size (get_channel conf (port_channel conf (pt (locals_' x !j))))
     ) \<and>
     channel_get_messages (the (chans (communication_' y) (port_channel conf (pt (locals_' x !j))))) = 
       B (port_channel conf (pt (locals_' x !j))) + channel_sent_messages  (port_channel conf (pt (locals_' x !j))) adds  (locals_' y) -
         channel_received_messages  (port_channel conf (pt (locals_' x !j))) rems  (locals_' y)  \<and>
   (\<forall>i. i\<noteq>j \<longrightarrow>  
        a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' y !i) ch_id \<and> 
        r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' y !i) ch_id)  
   )\<and>
   (\<forall>ch_id'. ch_id'\<noteq>ch_id \<longrightarrow>
      chans (communication_' x) ch_id' = chans (communication_' y) ch_id'\<and>
      (\<forall>i. a_que_aux (locals_' x !i) ch_id' = a_que_aux (locals_' y !i) ch_id' \<and>
           r_que_aux (locals_' x !i) ch_id' = r_que_aux (locals_' y !i) ch_id'))" *)
    
definition "Guarantee_mod_chan"
where
"Guarantee_mod_chan x y j \<equiv>    
  let ch = (port_channel conf  (communication_' x) (pt (locals_' x !j))) in
  (channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
    channel_get_messages (the (chans (communication_' y) ch)) \<and>
   p_queuing conf (communication_' x) (pt (locals_' x !j))  \<longrightarrow>
     port_open (communication_' x) (pt (locals_' x !j)) \<and>
    ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
     (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
     ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
        (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
           m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
          channel_get_messages (the (chans (communication_' y) ch)) = 
            channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
          a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
      (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
       a_que_aux (locals_' y !j) ch = 
         {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
       r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
        size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
         channel_size (get_channel conf ch) \<and>
       channel_get_messages (the (chans (communication_' y) ch)) = 
         channel_get_messages (the (chans (communication_' x) ch)) +   
         {#msg (locals_' x !j)#} ) 
     )) \<and>
   ((channel_get_messages (the (chans (communication_' x) ch)) =
    channel_get_messages (the (chans (communication_' y) ch)) \<or> 
    \<not> (p_queuing conf (communication_' x) (pt (locals_' x !j)))) \<longrightarrow>
          r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
          a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch)           
"   
lemma "(\<forall>ch_id. ch_id\<noteq>(port_channel conf (communication_' x) (pt (locals_' x !i))) \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id) \<Longrightarrow>
       (\<forall>ch_id. chans (communication_' x) ch_id \<noteq> chans (communication_' y) ch_id) \<longrightarrow>
                   ch_id=(port_channel conf (communication_' x) (pt (locals_' x !i)))"  
  by auto
    
lemma "(\<forall>ch_id. 
      (\<nexists>j. j<length (locals_' x1) \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) \<longrightarrow> 
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id)  \<Longrightarrow> 
     (\<forall>ch_id. 
      chans (communication_' x1) ch_id \<noteq> chans (communication_' y1) ch_id \<longrightarrow>
      (\<exists>j. j<length (locals_' x1) \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) 
      )" by auto

definition Guarantee_Send_Receive'
where
"Guarantee_Send_Receive' i   \<equiv> 
{(x,y). 
    let pch_id = port_channel conf (communication_' x) (pt (locals_' x !i)) in
    ports (communication_' x) = ports (communication_' y)  \<and>
   ({ch. chans (communication_' x) ch = None} = {ch. chans (communication_' y) ch = None}) \<and>
    ({ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} = 
      {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1}) \<and>
   ((\<exists>ch. chans (communication_' x) pch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
     (\<exists>ch. chans (communication_' y) pch_id =  Some ch \<and> chan_queuing ch)) \<and>  
    schedule (locals_' x !i) =  schedule (locals_' y !i) \<and>
   (\<forall>ch_id. ch_id\<noteq>pch_id \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id) \<and>       
   (\<forall>ch_id. (ch_id \<noteq> pch_id \<longrightarrow>
               (a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' y !i) ch_id) \<and> 
               (r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' y !i) ch_id))) \<and>     
    ((a_que_aux (locals_' x !i) \<noteq> a_que_aux (locals_' y !i) \<or> 
     (r_que_aux (locals_' x !i) \<noteq> r_que_aux (locals_' y !i))) \<longrightarrow>
       (mut (the (chans (communication_' x) pch_id)) = i + 1)
    ) \<and>
    (chans (communication_' x) pch_id\<noteq> chans (communication_' y) pch_id \<longrightarrow>
      (mut (the (chans (communication_' x) pch_id)) = i + 1 \<or> 
       mut (the (chans (communication_' y) pch_id)) = i + 1)) \<and> 
   (mut (the (chans (communication_' x) pch_id)) \<noteq> mut (the (chans (communication_' y) pch_id)) \<longrightarrow>
      (mut (the (chans (communication_' x) pch_id)) = 0 \<or> 
      mut (the (chans (communication_' y) pch_id)) = 0)) \<and>      
   Guarantee_mod_chan  x y i   
   }         
"

definition Guarantee_Send_Receive
where
"Guarantee_Send_Receive i   \<equiv> 
 {(x,y). (\<exists>x1 y1.      
    x=Normal x1 \<and> y=Normal y1 \<and> 
    length (locals_' x1) = length (locals_' y1) \<and>   
    evnt (locals_' x1 !i) = evnt (locals_' y1 !i) \<and> 
    pt (locals_' x1 !i) =  pt (locals_' y1 !i) \<and>
    (\<forall>j. (j\<noteq>i) \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j) \<and>      
    state_conf x1 = state_conf y1 \<and>                                 
    (x1,y1)\<in> Guarantee_Send_Receive' i    
  ) \<or> (x=y)             
 }  
"

definition Rely_mod_chan
  where
"Rely_mod_chan x y i \<equiv>
let ch = (port_channel conf  (communication_' x) (pt (locals_' x !i))) in
   ((channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
      channel_get_messages (the (chans (communication_' y) ch))) \<and>
     p_queuing conf  (communication_' x) (pt (locals_' x !i)) \<longrightarrow>      
     (\<exists>j<procs conf. 
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)
       )) \<and>      
    (((channel_get_messages (the (chans (communication_' x) ch)) =
      channel_get_messages (the (chans (communication_' y) ch))) \<or>
     \<not> p_queuing conf  (communication_' x) (pt (locals_' x !i)) \<longrightarrow>        
            (\<forall>j. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
                 a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch)))    
 "  
                 
definition Rely_Send_Receive:: "nat \<Rightarrow> ('b vars_scheme \<times> 'b vars_scheme) set"
where
"Rely_Send_Receive i   \<equiv>
 {(x,y).  
   let pch_id = port_channel conf (communication_' x) (pt (locals_' x !i)) in
   Rely_mod_chan x y i  \<and>
   ports (communication_' x) = ports (communication_' y) \<and>
   {ch. chans (communication_' x) ch = None} = 
     {ch. chans (communication_' y) ch = None} \<and>
   {ch. \<exists>ch1. chans (communication_' x) ch = Some ch1} = 
     {ch. \<exists>ch1. chans (communication_' y) ch = Some ch1} \<and>  
  (\<forall>ch_id.
    ((\<exists>ch. chans (communication_' x) ch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
     (\<exists>ch. chans (communication_' y) ch_id =  Some ch \<and> chan_queuing ch))) \<and>            
  ((mut (the (chans (communication_' x) pch_id)) = i + 1 \<or> 
   mut (the (chans (communication_' y) pch_id)) = i + 1)  \<longrightarrow>
      chans (communication_' x) pch_id = chans (communication_' y) pch_id \<and>
      (\<forall>j. (a_que_aux (locals_' x !j) pch_id) = (a_que_aux(locals_' y !j)) pch_id \<and>
           (r_que_aux (locals_' x !j) pch_id) = (r_que_aux(locals_' y !j)) pch_id)                         
   ) \<and>    
   (\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x) (pt (locals_' x !j))) \<longrightarrow> 
      chans (communication_' x) ch_id = chans (communication_' y) ch_id \<and>
       (\<forall>i.(a_que_aux (locals_' x !i) ch_id = a_que_aux (locals_' y !i) ch_id) \<and> 
           (r_que_aux (locals_' x !i) ch_id = r_que_aux (locals_' y !i) ch_id) )) \<and>       
   (mut (the (chans (communication_' x) pch_id)) \<noteq> i + 1 \<longrightarrow>
      mut (the (chans (communication_' y) pch_id)) \<noteq> i + 1)
    
 }
"

definition Rely_Send_ReceiveS::" nat \<Rightarrow> (('c vars_scheme, 'a) xstate \<times> ('c vars_scheme, 'a) xstate) set"
where
"Rely_Send_ReceiveS i   \<equiv> {(x,y). x=y}
"

definition Rely_Send_ReceiveQ :: " nat \<Rightarrow> (('c vars_scheme, 'a) xstate \<times> ('c vars_scheme, 'a) xstate) set"
where
"Rely_Send_ReceiveQ i   \<equiv>
  {(x,y). ((\<exists>x1 y1. 
           x=Normal x1 \<and> y = Normal y1 \<and>
           (locals_' x1)!i = (locals_' y1)!i \<and> 
           length (locals_' x1) = length (locals_' y1) \<and>
           (\<forall>j.  (evnt (locals_' x1 !j) = evnt (locals_' y1 !j)) \<and>
                    (pt (locals_' x1 !j) = pt (locals_' y1 !j))) \<and>   
            state_conf x1 = state_conf y1 \<and>                   
           ((x1,y1)\<in> Rely_Send_Receive i)
          ) \<or> x = y)
  }"

definition Rely :: " nat \<Rightarrow> (('c vars_scheme, 'a) xstate \<times> ('c vars_scheme, 'a) xstate) set"
where
"Rely i   \<equiv>                                             
  {(x,y). (x,y)\<in> Rely_Send_ReceiveQ i \<or> (x,y)\<in> Rely_Send_ReceiveS i
  }"


  
lemma Rely_eq_send:
  assumes a0':"i<length (locals_' x)" and        
         a1:"channel_received_messages  ch rems (locals_' x) \<subseteq># 
           (B ch + channel_sent_messages  ch adds  (locals_' x))" and  
         a2:"channel_get_messages (the (chans (communication_' x) ch)) = 
             (B ch + 
            channel_sent_messages  ch  adds (locals_' x) ) -
            channel_received_messages  ch  rems (locals_' x)" and
       a5:"channel_messages ch adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  ch a_que_aux (locals_' x)" and       
       a7:"(x,y,i)\<in>preserves_locals_constr"  and
       a8:"a_que_aux (locals_' y ! i) ch = {#msg (locals_' x ! i)#} + a_que_aux (locals_' x ! i) ch" and
       a9:"r_que_aux (locals_' x ! i) ch = r_que_aux (locals_' y ! i) ch"  and
       a10:"channel_get_messages (the (chans (communication_' y) ch)) = 
            channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x ! i)#}"
      shows "channel_get_messages (the (chans (communication_' y) ch)) =
    B ch + channel_sent_messages ch adds (locals_' y) - channel_received_messages ch rems (locals_' y)"
proof-  
  have eq_rec:"channel_received_messages  ch rems  (locals_' x) =
               channel_received_messages  ch rems  (locals_' y)" 
    using add_channel_message_not_evnt  a9 a7 preserves_locals_D1 
    unfolding channel_received_messages_def by fastforce   
  moreover have eq_send:"channel_messages  ch a_que_aux (locals_' x)  + 
                {#msg (locals_' x ! i)#} = channel_messages  ch a_que_aux (locals_' y)"      
    using a7 add_channel_message_evnt 
    by (metis a0' a8 union_commute)
  ultimately show ?thesis
  proof -
    have "channel_sent_messages ch adds (locals_' y) = 
          channel_messages ch a_que_aux (locals_' x) - 
              channel_messages ch adds [0..<length (locals_' y)] + {#msg (locals_' x ! i)#}"       
      by (metis (no_types) a5 a7 channel_sent_messages_def eq_send preserves_locals_D1 
        subset_mset.add_diff_assoc2)
    then have "B ch + 
              channel_sent_messages ch adds (locals_' y) = 
                B ch + 
                channel_sent_messages ch adds (locals_' x) + {#msg (locals_' x ! i)#}"
      by (metis (no_types) a7 ab_semigroup_add_class.add_ac(1) channel_sent_messages_def 
             preserves_locals_D1)
    then show ?thesis
      by (metis (no_types)  a1 a10 a2 eq_rec subset_mset.add_diff_assoc2)
  qed    
qed     
  
lemma Rely_subset_send:
  assumes a0':"i<length (locals_' x)" and        
         a1:"channel_received_messages  ch rems (locals_' x) \<subseteq># 
             B ch + channel_sent_messages  ch adds  (locals_' x)" and       
       a5:"channel_messages ch adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  ch a_que_aux (locals_' x)" and       
       a7:"(x,y,i)\<in>preserves_locals_constr" and
       a8:"a_que_aux (locals_' y ! i) ch = {#msg (locals_' x ! i)#} + a_que_aux (locals_' x ! i) ch" and
       a9:"r_que_aux (locals_' x ! i) ch = r_que_aux (locals_' y ! i) ch"        
      shows "channel_received_messages  ch rems (locals_' y) \<subseteq># 
            B ch + channel_sent_messages  ch adds  (locals_' y)"
proof-
  have eq_rec:"channel_received_messages  ch rems  (locals_' x) =
               channel_received_messages  ch rems  (locals_' y)" 
    using add_channel_message_not_evnt a9 a7 preserves_locals_D1 
    unfolding channel_received_messages_def by fastforce   
  moreover have eq_send:"channel_messages ch a_que_aux (locals_' x)  + 
                {#msg (locals_' x ! i)#} = channel_messages ch a_que_aux (locals_' y)"      
    using a7 add_channel_message_evnt
    by (metis a0' a8 union_commute)
  ultimately show ?thesis
    by (metis a1 a5 a7 add_msg_send channel_sent_messages_def preserves_locals_D1)
qed   


lemma Rely_eq_rec:
  assumes a0':"i<length (locals_' x)" and        
         a1:"channel_received_messages ch rems (locals_' x) \<subseteq># 
             B ch + 
             channel_sent_messages  ch adds  (locals_' x)" and  
         a2:"channel_get_messages (the (chans (communication_' x) ch)) = 
              B ch + channel_sent_messages ch  adds (locals_' x)  - 
               channel_received_messages ch  rems (locals_' x)" and
       a5:"channel_messages ch rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages ch r_que_aux (locals_' x)" and       
       a7:"(x,y,i)\<in>preserves_locals_constr" and
       a8:"r_que_aux (locals_' y ! i) ch = r_que_aux (locals_' x ! i) ch + m" and
       a9:"m \<subseteq># channel_get_messages (the (chans (communication_' x) ch))" and       
       a11:" a_que_aux (locals_' x ! i) ch = a_que_aux (locals_' y ! i) ch" and
       a10:"channel_get_messages (the (chans (communication_' y) ch)) =
          channel_get_messages (the (chans (communication_' x) ch)) - m"
      shows "channel_get_messages (the (chans (communication_' y) ch)) =
     B ch + channel_sent_messages ch adds (locals_' y) - 
     channel_received_messages ch rems (locals_' y)"
proof-
  have eq_rec:"channel_sent_messages ch adds  (locals_' x) =
                  channel_sent_messages ch adds  (locals_' y)" 
    using add_channel_message_not_evnt a11 a7 preserves_locals_D1
    unfolding  channel_sent_messages_def  by fastforce
  moreover have eq_send:"channel_messages ch r_que_aux (locals_' x)  + m  =
            channel_messages ch r_que_aux (locals_' y)"      
    using a7 add_channel_message_evnt
    by (metis a0' a8 union_commute)
  ultimately show ?thesis
    using a10 a2 a5 a7  preserves_locals_D1 unfolding channel_received_messages_def by fastforce 
 qed      
 

   
lemma Rely_subset_rec:
  assumes a0':"i<length (locals_' x)" and         
         a1:"channel_received_messages ch rems (locals_' x) \<subseteq># 
            B ch + channel_sent_messages ch adds  (locals_' x)" and       
       a3:"channel_get_messages (the (chans (communication_' x) ch)) = 
            B ch + channel_sent_messages ch  adds (locals_' x)  -
            channel_received_messages ch rems (locals_' x)" and
       a4:"channel_messages ch rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages ch r_que_aux (locals_' x)" and       
       a7:"(x,y,i)\<in>preserves_locals_constr" and
       a8:"r_que_aux (locals_' y ! i) ch = r_que_aux (locals_' x ! i) ch + m" and
       a9:"m \<subseteq># channel_get_messages (the (chans (communication_' x) ch))" and       
       a11:" a_que_aux (locals_' x ! i) ch = a_que_aux (locals_' y ! i) ch"               
      shows "channel_received_messages  ch rems (locals_' y) \<subseteq># 
           (B ch + channel_sent_messages ch adds  (locals_' y))"
proof-
  have "channel_messages ch r_que_aux (locals_' x)  + m  =
            channel_messages ch r_que_aux (locals_' y)"      
     using a0' a7 a8 add_channel_message_evnt by blast               
    moreover have "channel_sent_messages ch adds  (locals_' x) =
                  channel_sent_messages ch adds  (locals_' y)"
      using add_channel_message_not_evnt a11 a7
      using channel_sent_messages_def preserves_locals_D1 by fastforce   
    moreover have "m\<subseteq>#(B ch + 
             channel_sent_messages ch adds  (locals_' y)) -
             channel_received_messages ch rems  (locals_' x)"
      using a3  a9 calculation(2) by auto  
    ultimately show ?thesis using a1  a4  add_msg_rec a7 preserves_locals_D1
      unfolding  channel_received_messages_def by fastforce        
 qed      

lemma Rely_subset:
  assumes a0:"p_queuing conf (communication_' x) (pt (locals_' x ! i))" and           
         a1:"channel_received_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) rems (locals_' x) \<subseteq># 
           (B (port_channel conf (communication_' x) (pt (locals_' x !i))) + 
             channel_sent_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) adds  (locals_' x))" and
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and
       a3:"channel_get_messages (the (chans (communication_' x)  (port_channel conf (communication_' x) (pt (locals_' x !i))))) = 
             (B (port_channel conf (communication_' x) (pt (locals_' x !i))) + 
            channel_sent_messages  (port_channel conf (communication_' x) (pt (locals_' x !i)))  adds (locals_' x) ) -
            channel_received_messages  (port_channel conf (communication_' x) (pt (locals_' x !i)))  rems (locals_' x)" and
       a4:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) r_que_aux (locals_' x)" and
       a5:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) a_que_aux (locals_' x)"  and
       a6:"procs conf = length (locals_' x)"
      shows "channel_received_messages  (port_channel conf (communication_' y) (pt (locals_' x !i))) rems (locals_' y) \<subseteq># 
           (B (port_channel conf (communication_' y) (pt (locals_' x !i))) + 
             channel_sent_messages  (port_channel conf (communication_' y) (pt (locals_' x !i))) adds  (locals_' y))"
proof (cases 
    "channel_get_messages (the (chans (communication_' x) (port_channel conf (communication_' x) (pt (locals_' x !i))))) \<noteq>
      channel_get_messages (the (chans (communication_' y) (port_channel conf (communication_' y) (pt (locals_' x !i)))))")                  
  case True            
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) =
                  port_channel conf (communication_' x) (pt (locals_' x ! i))" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast
  note b0 = mp [OF conjunct1[OF relchan[simplified Rely_mod_chan_def Let_def]]  
                   conjI[OF True[simplified portch_eq] a0] ]  
  then obtain j where 
   b0: "j<procs conf \<and>
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)"      
     using ch_def by blast     
    have pre_local:"length (locals_' x) = length (locals_' y) \<and>
          (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' y)!i') \<and>
                pt ((locals_' x)!i') = pt ((locals_' y)!i'))"
      using a2 unfolding Rely_Send_ReceiveQ_def by auto       
    have preserves:"(x,y,j)\<in>preserves_locals_constr"
      using pre_local b0 unfolding preserves_locals_constr_def by auto
  { assume "r_que_aux (locals_' y ! j) ch \<noteq> r_que_aux (locals_' x ! j) ch"
    then obtain m where 
      mod:"(r_que_aux (locals_' y ! j) ch =
        r_que_aux (locals_' x ! j) ch + m \<and>
        m \<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
        channel_get_messages (the (chans (communication_' y) ch)) =
          channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
        a_que_aux (locals_' x ! j) ch =
          a_que_aux (locals_' y ! j) ch \<and>
       (\<forall>ch_id. ch_id \<noteq> ch \<longrightarrow>
                  a_que_aux (locals_' x ! j) ch_id = a_que_aux (locals_' y ! j) ch_id \<and>
                  r_que_aux (locals_' x ! j) ch_id = r_que_aux (locals_' y ! j) ch_id)" 
      using b0 by blast          
    have ?thesis 
      using mod
         Rely_subset_rec[of j x "(port_channel conf (communication_' x) (pt (locals_' x ! i)))" rems B adds _ m, 
                          OF _ a1 a3 a4 preserves ]          
      using b0[unfolded a6] by (simp add: portch_eq)       
  }
  moreover { assume "a_que_aux (locals_' y ! j) ch \<noteq> a_que_aux (locals_' x ! j) ch"
    then have 
       mod:"a_que_aux (locals_' y ! j) ch =
           {#msg (locals_' x ! j)#} + a_que_aux (locals_' x ! j) ch \<and>
           r_que_aux (locals_' x ! j) ch = r_que_aux (locals_' y ! j) ch \<and>
           size (channel_get_messages (the (chans (communication_' y) ch)))
             \<le> channel_size (get_channel conf ch) \<and>
           channel_get_messages (the (chans (communication_' y) ch)) =
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x ! j)#}" 
      using b0 by blast                 
      have ?thesis 
      using mod
         Rely_subset_send[of j x "(port_channel conf (communication_' x) (pt (locals_' x ! i)))" rems B adds, 
                          OF _ a1 a5 preserves]
      using b0[unfolded a6] by (simp add: portch_eq)       
  }
  ultimately show ?thesis using b0 by fastforce
next
  case False    
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) = ch" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast  
  then have b0:"(\<forall>j. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
                  a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch)"
    using False portch_eq unfolding Rely_mod_chan_def Let_def by auto 
      have pre_local:"length (locals_' x) = length (locals_' y) \<and>
        (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' y)!i') \<and>
              pt ((locals_' x)!i') = pt ((locals_' y)!i'))"
        using a2 unfolding Rely_Send_ReceiveQ_def by auto            
  have preserves:"(x,y,i)\<in>preserves_locals_constr'"
    using pre_local b0 portch_eq unfolding preserves_locals_constr'_def  by auto  
  then show ?thesis using False a1 portch_eq channel_messages_eq'[OF preserves]  pre_local b0
    unfolding channel_received_messages_def channel_sent_messages_def 
    by (simp add: pre_local)      
  qed
        
lemma Rely_chan_eq:
 assumes a0:"p_queuing conf  (communication_' x) (pt (locals_' x ! i))" and
         a1:"channel_received_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) rems (locals_' x) \<subseteq># 
           (B (port_channel conf  (communication_' x) (pt (locals_' x !i))) + 
             channel_sent_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) adds  (locals_' x))" and
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and
       a3:"channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i))))) = 
             (B (port_channel conf  (communication_' x) (pt (locals_' x !i))) + 
            channel_sent_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i)))  adds (locals_' x) ) -
            channel_received_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i)))  rems (locals_' x)" and
       a4:"channel_messages (port_channel conf  (communication_' x) (pt (locals_' x !i))) rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) r_que_aux (locals_' x)" and
       a5:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) a_que_aux (locals_' x)" and
       a6:"procs conf = length (locals_' x)"
      shows "channel_get_messages (the (chans (communication_' y) (port_channel conf (communication_' y) (pt (locals_' x !i))))) = 
             (B (port_channel conf  (communication_' y) (pt (locals_' x !i))) + 
            channel_sent_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i)))  adds (locals_' y) ) -
            channel_received_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i)))  rems (locals_' y)"
proof (cases 
    "channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i))))) \<noteq>
      channel_get_messages (the (chans (communication_' y) (port_channel conf (communication_' y) (pt (locals_' x !i)))))")
  case True
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) =
                  port_channel conf (communication_' x) (pt (locals_' x ! i))" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast
  note b0 = mp [OF conjunct1[OF relchan[simplified Rely_mod_chan_def Let_def]]  
                   conjI[OF True[simplified portch_eq] a0] ]  
  then obtain j where 
   b0: "j<procs conf \<and>
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)"      
     using ch_def by blast     
    have pre_local:"length (locals_' x) = length (locals_' y) \<and>
          (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' y)!i') \<and>
                pt ((locals_' x)!i') = pt ((locals_' y)!i'))"
      using a2 unfolding Rely_Send_ReceiveQ_def by auto        
    have preserves:"(x,y,j)\<in>preserves_locals_constr"
      using pre_local b0 unfolding preserves_locals_constr_def by auto
  { assume "r_que_aux (locals_' y ! j) ch \<noteq> r_que_aux (locals_' x ! j) ch"
    then obtain m where 
    mod:"(r_que_aux (locals_' y ! j) ch =
        r_que_aux (locals_' x ! j) ch + m \<and>
        m \<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
        channel_get_messages (the (chans (communication_' y) ch)) =
          channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
        a_que_aux (locals_' x ! j) ch =
          a_que_aux (locals_' y ! j) ch \<and>
       (\<forall>ch_id. ch_id \<noteq> ch \<longrightarrow>
                  a_que_aux (locals_' x ! j) ch_id = a_que_aux (locals_' y ! j) ch_id \<and>
                  r_que_aux (locals_' x ! j) ch_id = r_que_aux (locals_' y ! j) ch_id)" 
      using b0 by blast 
    have ?thesis                          
      using mod 
         Rely_eq_rec[of j x "(port_channel conf (communication_' x) (pt (locals_' x ! i)))" rems B adds, 
                          OF _ a1 a3 a4 preserves]
      using b0[unfolded a6] by (simp add: portch_eq)  
  }
  moreover { assume "a_que_aux (locals_' y ! j) ch \<noteq> a_que_aux (locals_' x ! j) ch"
    then have 
       mod:"a_que_aux (locals_' y ! j) ch =
           {#msg (locals_' x ! j)#} + a_que_aux (locals_' x ! j) ch \<and>
           r_que_aux (locals_' x ! j) ch = r_que_aux (locals_' y ! j) ch \<and>
           size (channel_get_messages (the (chans (communication_' y) ch)))
             \<le> channel_size (get_channel conf ch) \<and>
           channel_get_messages (the (chans (communication_' y) ch)) =
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x ! j)#}" 
      using b0 by blast                 
      have ?thesis 
      using mod
         Rely_eq_send[of j x "(port_channel conf (communication_' x) (pt (locals_' x ! i)))" rems B adds, 
                          OF _ a1 a3 a5 preserves]
      using b0[unfolded a6] by (simp add: portch_eq) 
  }
  ultimately show ?thesis using b0 by fastforce 
next
  case False
    define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) = ch" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast  
  then have b0:"(\<forall>j. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
                  a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch)"
    using False portch_eq unfolding Rely_mod_chan_def Let_def by auto 
      have pre_local:"length (locals_' x) = length (locals_' y) \<and>
        (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' y)!i') \<and>
              pt ((locals_' x)!i') = pt ((locals_' y)!i'))"
        using a2 unfolding Rely_Send_ReceiveQ_def by auto            
  have preserves:"(x,y,i)\<in>preserves_locals_constr'"
    using pre_local b0 portch_eq unfolding preserves_locals_constr'_def  by auto                
    then show ?thesis using False a1 portch_eq channel_messages_eq'[OF preserves]      
      using a3 channel_received_messages_def channel_sent_messages_def pre_local by auto      
  qed
    
lemma Rely_size:
 assumes a0:"p_queuing conf  (communication_' x) (pt (locals_' x ! i))" and         
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and
       a5':"size (channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i)))))) \<le> 
             channel_size (get_channel conf (port_channel conf  (communication_' x) (pt (locals_' x !i))))" and
       a6:"procs conf = length (locals_' x)"
      shows "size (channel_get_messages (the (chans (communication_' y) (port_channel conf  (communication_' y) (pt (locals_' x !i)))))) \<le> 
             channel_size (get_channel conf (port_channel conf  (communication_' y) (pt (locals_' x !i))))"
proof (cases 
    "channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i))))) \<noteq>
      channel_get_messages (the (chans (communication_' y) (port_channel conf (communication_' y) (pt (locals_' x !i)))))")
  case True
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) =
                  port_channel conf (communication_' x) (pt (locals_' x ! i))" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast
  note b0 = mp [OF conjunct1[OF relchan[simplified Rely_mod_chan_def Let_def]]  
                   conjI[OF True[simplified portch_eq] a0] ]  
  then obtain j where 
   b0: "j<procs conf \<and>
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)"      
     using ch_def by blast        
  { assume "r_que_aux (locals_' y ! j) ch \<noteq> r_que_aux (locals_' x ! j) ch"
    then obtain m where 
    mod:"(r_que_aux (locals_' y ! j) ch =
        r_que_aux (locals_' x ! j) ch + m \<and>
        m \<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
        channel_get_messages (the (chans (communication_' y) ch)) =
          channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
        a_que_aux (locals_' x ! j) ch =
          a_que_aux (locals_' y ! j) ch \<and>
       (\<forall>ch_id. ch_id \<noteq> ch \<longrightarrow>
                  a_que_aux (locals_' x ! j) ch_id = a_que_aux (locals_' y ! j) ch_id \<and>
                  r_que_aux (locals_' x ! j) ch_id = r_que_aux (locals_' y ! j) ch_id)" 
      using b0 by blast 
    have ?thesis
      by (metis a5' ch_def diff_subset_eq_self dual_order.trans mod portch_eq size_mset_mono)                                
  }
  moreover { assume "a_que_aux (locals_' y ! j) ch \<noteq> a_que_aux (locals_' x ! j) ch"
    then have 
       mod:"a_que_aux (locals_' y ! j) ch =
           {#msg (locals_' x ! j)#} + a_que_aux (locals_' x ! j) ch \<and>
           r_que_aux (locals_' x ! j) ch = r_que_aux (locals_' y ! j) ch \<and>
           size (channel_get_messages (the (chans (communication_' y) ch)))
             \<le> channel_size (get_channel conf ch) \<and>
           channel_get_messages (the (chans (communication_' y) ch)) =
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x ! j)#}" 
      using b0 by blast                 
      then have ?thesis unfolding ch_def using portch_eq by auto           
  }
  ultimately show ?thesis using b0 by fastforce 
next
  case False
    define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) = ch" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto  
  then show ?thesis
      using False a5' portch_eq by auto      
  qed    
    


lemma Rely_chan_subset1:
  assumes 
       a1:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) r_que_aux (locals_' x)" and
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and a3:"procs conf = length (locals_' x)"               
      shows "channel_messages (port_channel conf  (communication_' y) (pt (locals_' x !i))) rems [0..<length (locals_' y)] \<subseteq># 
               channel_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i))) r_que_aux (locals_' y) " 
proof-
  have len:"length (locals_' x) = length (locals_' y)" using a2 unfolding Rely_Send_ReceiveQ_def by auto 
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) = ch" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast  
  {
    assume True:"channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
            channel_get_messages (the (chans (communication_' y) ch)) \<and>
            p_queuing conf (communication_' x) (pt (locals_' x !i))"
    note b0 = mp [OF conjunct1[OF relchan[simplified Rely_mod_chan_def Let_def]]  
                   True[simplified ch_def]]
    then obtain j where 
     b0: "j<procs conf \<and>
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)"      
     using ch_def by blast         
    {assume "r_que_aux (locals_' y ! j) ch \<noteq> r_que_aux (locals_' x ! j) ch"
      then obtain m where
        "r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m" 
        using b0 by fast
      then have ?thesis
        by (metis  a3 a1 add_message_channel  portch_eq b0 ch_def len mset_subset_eq_add_left 
            subset_mset.add_increasing2 subset_mset.le_add_same_cancel1)        
    }
    moreover {assume "r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch"
      then have "\<forall>j. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch"
        using b0 portch_eq by metis
      then have ?thesis using len a1  same_channel_messages portch_eq ch_def by metis 
     }
     ultimately have ?thesis by auto
  }       
  moreover
  { assume ass0: 
           "channel_get_messages (the (chans (communication_' x) ch)) =
            channel_get_messages (the (chans (communication_' y) ch)) \<or>
            \<not>p_queuing conf (communication_' x) (pt (locals_' x !i))"       
    then have "\<forall>j. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch"
      using relchan  unfolding Rely_mod_chan_def Let_def by auto
    then have ?thesis using len a1 portch_eq ch_def same_channel_messages by metis 
  }
  ultimately show ?thesis by auto      
qed
  
lemma Rely_chan_subset2:
  assumes        
       a1:"channel_messages (port_channel conf  (communication_' x) (pt (locals_' x !i))) adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) a_que_aux (locals_' x)" and
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and a3:"procs conf = length (locals_' x)"                     
      shows "channel_messages (port_channel conf (communication_' y) (pt (locals_' x !i))) adds [0..<length (locals_' y)] \<subseteq># 
               channel_messages  (port_channel conf (communication_' y) (pt (locals_' x !i))) a_que_aux (locals_' y)" 
  proof-
  have len:"length (locals_' x) = length (locals_' y)" using a2 unfolding Rely_Send_ReceiveQ_def by auto 
  define ch where "ch = port_channel conf (communication_' x) (pt (locals_' x !i))" 
  note [simp] = ch_def    
  have portch_eq:"port_channel conf (communication_' y) (pt (locals_' x ! i)) = ch" 
    using a2 port_channl_eq_ports[THEN sym] 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
  have relchan:"Rely_mod_chan x y i"    
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Rely_mod_chan_def Let_def
    by fast  
  {
    assume True:"channel_get_messages (the (chans (communication_' x) ch)) \<noteq>
            channel_get_messages (the (chans (communication_' y) ch)) \<and>
            p_queuing conf (communication_' x) (pt (locals_' x !i))"
    note b0 = mp [OF conjunct1[OF relchan[simplified Rely_mod_chan_def Let_def]]  
                   True[simplified ch_def]]
    then obtain j where 
     b0: "j<procs conf \<and>
        port_open (communication_' x) (pt (locals_' x !j)) \<and>
       ch =  (port_channel conf (communication_' x) (pt (locals_' x !j))) \<and>
        ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch) \<or> 
         (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch)) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) + {#msg (locals_' x !j)#} ) 
       ) \<and> (\<forall>k. k\<noteq>j \<longrightarrow> locals_' x !k = locals_' y !k) \<and> 
       (\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow> 
          a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id \<and>
          r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)"      
      using ch_def by blast      
    have pre_local:"length (locals_' x) = length (locals_' y) \<and>
          (\<forall>i'. evnt ((locals_' x)!i') = evnt ((locals_' y)!i') \<and>
                pt ((locals_' x)!i') = pt ((locals_' y)!i'))"
      using a2 unfolding Rely_Send_ReceiveQ_def by auto       
    have preserves:"(x,y,j)\<in>preserves_locals_constr"
      using pre_local b0 unfolding preserves_locals_constr_def by auto
    {assume "a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch"
      then obtain m where
        "a_que_aux (locals_' y !j) ch = 
         a_que_aux (locals_' x !j) ch + m" 
        using b0 by force
      then have ?thesis
        by (metis a3 a1 add_message_channel portch_eq len b0 ch_def mset_subset_eq_add_left 
                  subset_mset.add_increasing2 subset_mset.le_add_same_cancel1)
    }
    moreover {assume "a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch"
      then have "\<forall>j. a_que_aux (locals_' y !j) ch =
                     a_que_aux (locals_' x !j) ch"
        using b0 ch_def portch_eq by metis
      then have ?thesis using len a1  same_channel_messages portch_eq ch_def 
        by metis 
     }
     ultimately have ?thesis by auto
  }       
  moreover
  { assume ass0: "channel_get_messages (the (chans (communication_' x) ch)) =
            channel_get_messages (the (chans (communication_' y) ch)) \<or>
            \<not>p_queuing conf (communication_' x) (pt (locals_' x !i))"
    then have "\<forall>j. a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch"
      using relchan unfolding Rely_mod_chan_def Let_def by auto    
    then have ?thesis using len a1 portch_eq ch_def same_channel_messages by metis 
  }
  ultimately show ?thesis by auto      
qed
  
lemma Rely_chan_subset:
  assumes        
       a1:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) r_que_aux (locals_' x)" and
       a2:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf (communication_' x) (pt (locals_' x !i))) a_que_aux (locals_' x)" and        
       a3:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and a4:"procs conf = length (locals_' x)"
      shows "channel_messages (port_channel conf (communication_' y) (pt (locals_' x !i))) rems [0..<length (locals_' y)] \<subseteq># 
               channel_messages  (port_channel conf (communication_' y) (pt (locals_' x !i))) r_que_aux (locals_' y) \<and>
             channel_messages (port_channel conf (communication_' y) (pt (locals_' x !i))) adds [0..<length (locals_' y)] \<subseteq># 
               channel_messages  (port_channel conf (communication_' y) (pt (locals_' x !i))) a_que_aux (locals_' y)"  
  using a1 a2 a3 a4 Rely_chan_subset1 Rely_chan_subset2 by blast

lemma Rely_chan_spec:
   assumes a0:"p_queuing conf  (communication_' x) (pt (locals_' x ! i))" and
         a1:"channel_received_messages  (port_channel conf (communication_' x)  (pt (locals_' x !i))) rems (locals_' x) \<subseteq># 
           (B (port_channel conf  (communication_' x) (pt (locals_' x !i))) + 
             channel_sent_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) adds  (locals_' x))" and
       a2:"(Normal x,Normal y)\<in>  Rely_Send_ReceiveQ i  " and
       a3:"channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i))))) = 
             (B (port_channel conf  (communication_' x) (pt (locals_' x !i))) + 
            channel_sent_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i)))  adds (locals_' x) ) -
            channel_received_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i)))  rems (locals_' x)" and
       a4:"channel_messages (port_channel conf  (communication_' x) (pt (locals_' x !i))) rems [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) r_que_aux (locals_' x)" and
       a5:"channel_messages (port_channel conf (communication_' x) (pt (locals_' x !i))) adds [0..<length (locals_' x)] \<subseteq># 
           channel_messages  (port_channel conf  (communication_' x) (pt (locals_' x !i))) a_que_aux (locals_' x)" and
       a5':"size (channel_get_messages (the (chans (communication_' x) (port_channel conf  (communication_' x) (pt (locals_' x !i)))))) \<le> 
             channel_size (get_channel conf (port_channel conf  (communication_' x) (pt (locals_' x !i))))" and
       a6:"procs conf = length (locals_' x)"
      shows "channel_get_messages (the (chans (communication_' y) (port_channel conf  (communication_' y) (pt (locals_' x !i))))) = 
             (B (port_channel conf  (communication_' y) (pt (locals_' x !i))) + 
            channel_sent_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i)))  adds (locals_' y) ) -
            channel_received_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i)))  rems (locals_' y) \<and>
            channel_received_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i))) rems (locals_' y) \<subseteq># 
           (B (port_channel conf  (communication_' y) (pt (locals_' x !i))) + 
             channel_sent_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i))) adds  (locals_' y)) \<and>
           size (channel_get_messages (the (chans (communication_' y) (port_channel conf  (communication_' y) (pt (locals_' x !i)))))) \<le> 
             channel_size (get_channel conf (port_channel conf  (communication_' y) (pt (locals_' x !i)))) \<and>
           channel_messages (port_channel conf  (communication_' y) (pt (locals_' x !i))) rems [0..<length (locals_' y)] \<subseteq># 
                   channel_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i))) r_que_aux (locals_' y) \<and>
                 channel_messages (port_channel conf  (communication_' y) (pt (locals_' x !i))) adds [0..<length (locals_' y)] \<subseteq># 
                   channel_messages  (port_channel conf  (communication_' y) (pt (locals_' x !i))) a_que_aux (locals_' y)"
  using Rely_chan_eq[OF a0,of rems B, OF a1 a2 a3 a4 a5 a6] 
        Rely_subset[OF a0, of rems B, OF a1 a2 a3 a4 a5 a6]
        Rely_size[OF a0 a2  a5' a6]
        Rely_chan_subset1 Rely_chan_subset2 a2 a4 a5 a6 by blast
    
lemma rely_eq_channel:"         
          mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = Suc i \<Longrightarrow>  
          (Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i  \<Longrightarrow>
            (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) a_que_aux  (locals_' x1) )  = 
            (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) a_que_aux (locals_' y1))  \<and>
            (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) r_que_aux  (locals_' x1) )  = 
            (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) r_que_aux (locals_' y1) ) "
proof-
 let ?p = "port_channel conf (communication_' x1) (pt (locals_' x1 !i))"
 assume
        a1:"mut (the (chans (communication_' x1) ?p)) = Suc i" and
        a2:"(Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i "
  have ports:"ports (communication_' x1) = ports (communication_' y1)"
      using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto  
  have f1:"locals_' x1 ! i = locals_' y1 ! i" using a2 unfolding Rely_Send_ReceiveQ_def by auto
  moreover have f2:" \<forall>j. evnt (locals_' x1 ! j) = evnt (locals_' y1 ! j) \<and> 
                         pt (locals_' x1 ! j) = pt (locals_' y1 ! j)" 
    using a2 unfolding Rely_Send_ReceiveQ_def by auto
  moreover then have "(\<forall>j. (a_que_aux (locals_' x1 !j) ?p) = (a_que_aux(locals_' y1 !j)) ?p \<and>
                            (r_que_aux (locals_' x1 !j) ?p) = (r_que_aux(locals_' y1 !j)) ?p)"    
  using a1 a2  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def apply simp by blast
  moreover have "length (locals_' x1) = length (locals_' y1)" 
    using a2 unfolding Rely_Send_ReceiveQ_def by auto  
  ultimately show ?thesis
    using same_channel_messages port_channl_eq_ports[OF ports]
    by (simp add: same_channel_messages) 
qed
  
lemma rely_eq_ports1:"(Normal x1,  y) \<in> Rely_Send_ReceiveQ i \<Longrightarrow>
       \<exists>y1. y=Normal y1 \<and> ports (communication_' x1) = ports (communication_' y1) \<and>
       pt (locals_' x1 !i) = pt (locals_' y1 !i)"   
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto

lemma rely_eq_ports:"(Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i \<Longrightarrow>
       ports (communication_' x1) = ports (communication_' y1) \<and>
       pt (locals_' x1 !i) = pt (locals_' y1 !i)"   
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto    
    
lemma rely_eq_channel_inits:"         
          mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = Suc i \<Longrightarrow>  
          (Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i  \<Longrightarrow>
            (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) a_que_aux  (locals_' x1) ) -
             (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) adds [0..< (length (locals_' x1))]) = 
            (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) a_que_aux (locals_' y1) -
             (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) adds [0..< (length (locals_' y1))])) \<and>
            (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) r_que_aux  (locals_' x1) ) -
             (channel_messages (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) rems [0..< (length (locals_' x1))]) = 
            (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) r_que_aux (locals_' y1) ) -
             (channel_messages (port_channel conf (communication_' y1) (pt (locals_' y1 ! i))) rems [0..< (length (locals_' y1))])"
  apply (drule rely_eq_channel,assumption)
  apply (frule rely_eq_ports)
  apply clarsimp     
  apply (frule port_channl_eq_ports[of _ _ i]) 
  unfolding Rely_Send_ReceiveQ_def by force
  

lemma rely_eq_queue:"
          (p_queuing conf (communication_' x1) (pt (locals_' x1 ! i))) \<Longrightarrow>         
          mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = Suc i \<Longrightarrow>  
          (Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i  \<Longrightarrow>
          chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) = 
          chans (communication_' y1) (port_channel conf (communication_' y1) (pt (locals_' x1 !i)))"
proof-
  assume a0: "(p_queuing conf (communication_' x1) (pt (locals_' x1 ! i)))" and
        a1:"mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = Suc i" and
        a2:"(Normal x1, Normal y1) \<in> Rely_Send_ReceiveQ i "        
  thus ?thesis unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def    
    apply simp       
    by (metis (no_types, lifting) port_channl_eq_ports)
      
qed
  
subsection {* lemmas on reflexivity of Rely\_Send*}
  
lemma reflexive_Guarantee_Send:
  "( s,  s) \<in> Guarantee_Send_Receive i"
  unfolding Guarantee_Send_Receive_def Guarantee_Send_Receive'_def 
            Guarantee_mod_chan_def
  by auto

lemma reflexive_rely_send:
  "(a,a) \<in> Rely_Send_ReceiveQ i"
  unfolding Rely_Send_ReceiveQ_def
  by auto



lemma sta_ch_spec_mut:" 
           Sta (\<lbrace>p_queuing conf  \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>                 
                \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                {x.  ch_spec B adds rems (port_channel conf (communication_' x) (pt ((locals_' x) ! i))) x})
             (Rely_Send_ReceiveQ i )"
unfolding  Sta_def 
proof clarify
  fix i y x'
  assume
   a0:"ch_spec B adds rems (port_channel conf (communication_' (x'::'a vars_scheme)) (pt (locals_' x' ! i))) x'" and
   a1:"p_queuing conf (communication_' x') (pt (locals_' x' ! i))" and
   a2:"port_get_mutex conf (communication_' x') (pt (locals_' x' ! i)) = Suc i" and
   a3:"(Normal x', (y::('a vars_scheme, 'b) xstate)) \<in> Rely_Send_ReceiveQ i  " 
  then obtain y' where y:"y=Normal y' \<and> length (locals_' x') = length (locals_' y')" 
    unfolding Rely_Send_ReceiveQ_def by auto
  have eq_chan:"channel_messages (port_channel conf (communication_' x') (pt (locals_' x' ! i))) a_que_aux  (locals_' x') = 
                channel_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) a_que_aux  (locals_' y') \<and>
                channel_messages (port_channel conf (communication_' x') (pt (locals_' x' ! i))) r_que_aux  (locals_' x') = 
                channel_messages (port_channel conf(communication_' y')  (pt (locals_' y' ! i))) r_que_aux  (locals_' y')"
    using rely_eq_channel[OF a2[simplified port_get_mutex_def channel_get_mutex_def Let_def] a3[simplified y]]  
    by auto
  also have eq_q:"chans (communication_' x') (port_channel conf (communication_' x') (pt (locals_' x' !i))) = 
                  chans (communication_' y') (port_channel conf (communication_' y') (pt (locals_' x' !i)))"
  using rely_eq_queue[OF a1]  using a1 a2 a3 y 
    unfolding port_get_mutex_def channel_get_mutex_def by fastforce
  have eq_locals:"locals_' x' !i = locals_' y'!i" using a3 y unfolding Rely_Send_ReceiveQ_def by auto
  then have eq:"pt (locals_' x' !i) = pt(locals_' y'!i)" by auto
  have f1:"p_queuing conf (communication_' y') (pt (locals_' y' ! i))" using a1 y a3 unfolding Rely_def
    by (metis (no_types, lifting) a3 p_queuing_def port_channl_eq_ports rely_eq_ports)
  have f2:"port_get_mutex conf (communication_' y') (pt (locals_' y' ! i)) = Suc i"
    using a1 a2 a3 y
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def  
              port_get_mutex_def channel_get_mutex_def Let_def              
    using eq_q by fastforce    
  have f3:"ch_spec B adds rems (port_channel conf (communication_' y') (pt (locals_' y' ! i))) y'"
    using a0 eq_chan eq_q eq_locals y
    unfolding ch_spec_def  
        channel_received_messages_def channel_sent_messages_def
    by (metis a3 port_channl_eq_ports rely_eq_ports)            
  then show "\<exists>y'. y = Normal y' \<and>
            y' \<in> \<lbrace>p_queuing conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>                  
                 \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                  {x. ch_spec B adds rems (port_channel conf (communication_' x) (pt (locals_' x ! i))) x}"
   using y f1 f2 f3 by auto
qed
    


lemma sta_send_mod_que:"Sta
          (\<lbrace>p_queuing conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter>           
           \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
           \<lbrace>channel_get_messages (the (chans \<acute>communication (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))) =
            add_mset (msg (\<acute>locals ! i))
             (B (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) + 
             channel_sent_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds \<acute>locals -
             channel_received_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) rems \<acute>locals) \<and>
           channel_received_messages  (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) rems \<acute>locals  \<subseteq>#
            B (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) + 
              channel_sent_messages  (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds \<acute>locals \<and>
            size (channel_get_messages  (the (chans \<acute>communication (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))))
            \<le> channel_size (get_channel conf (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))\<rbrace>)
          (Rely_Send_ReceiveQ i )
" 
unfolding  Sta_def 
proof clarify
  fix i y x'
assume
   a1:"p_queuing conf (communication_' x') (pt (locals_' (x'::'a vars_scheme) ! i))" and
   a2:"port_get_mutex conf (communication_' x') (pt (locals_' x' ! i)) = Suc i" and
   a3:"(Normal x', (y::('a vars_scheme, 'b) xstate)) \<in> Rely_Send_ReceiveQ i   " and  
   a4:"channel_get_messages (the (chans (communication_' x') (port_channel conf (communication_' x') (pt (locals_' x' ! i))))) =
       add_mset (msg (locals_' x' ! i))
        (B (port_channel conf (communication_' x') (pt (locals_' x' ! i))) + 
         channel_sent_messages (port_channel conf  (communication_' x') (pt (locals_' x' ! i))) adds (locals_' x') -
         channel_received_messages (port_channel conf (communication_' x') (pt (locals_' x' ! i))) rems (locals_' x'))" and
   a5:"channel_received_messages  (port_channel conf (communication_' x') (pt (locals_' x' ! i))) rems (locals_' x')  \<subseteq>#
        B (port_channel conf (communication_' x') (pt (locals_' x' ! i))) + 
          channel_sent_messages  (port_channel conf (communication_' x') (pt (locals_' x' ! i))) adds  (locals_' x')" and 
   a6:"size (channel_get_messages  (the (chans (communication_' x') (port_channel conf (communication_' x') (pt (locals_' x' ! i))))))
        \<le> channel_size (get_channel conf (port_channel conf (communication_' x') (pt (locals_' x' ! i))))" 
  then obtain y' where y:"y=Normal y' \<and> length (locals_' x') = length (locals_' y')" 
    unfolding Rely_Send_ReceiveQ_def by auto
  have port_chan:"port_channel conf (communication_' x') (pt (locals_' x' ! i)) = port_channel conf (communication_' y') (pt (locals_' x' ! i))"
    using port_channl_eq_ports rely_eq_ports using a3 y by blast   
  have eq_chan:"(channel_messages  (port_channel conf (communication_' x') (pt (locals_' x' ! i))) a_que_aux (locals_' x') ) -
                 (channel_messages (port_channel conf (communication_' x') (pt (locals_' x' ! i))) adds [0..< (length (locals_' x'))]) = 
                (channel_messages  (port_channel conf(communication_' y')  (pt (locals_' y' ! i))) a_que_aux  (locals_' y'))-
                 (channel_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) adds [0..< (length (locals_' y'))]) \<and>
                 (channel_messages  (port_channel conf (communication_' x') (pt (locals_' x' ! i))) r_que_aux (locals_' x') )-
                 (channel_messages (port_channel conf (communication_' x') (pt (locals_' x' ! i))) rems [0..< (length (locals_' x'))]) = 
                 (channel_messages  (port_channel conf (communication_' y') (pt (locals_' y' ! i))) r_que_aux  (locals_' y'))-
                 (channel_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) rems [0..< (length (locals_' y'))])"
    using rely_eq_channel_inits using a1 a2 a3 y 
    unfolding port_get_mutex_def  Let_def channel_get_mutex_def by blast
  also have eq_q:"chans (communication_' x') (port_channel conf (communication_' x') (pt (locals_' x' !i))) = 
                  chans (communication_' y') (port_channel conf (communication_' y') (pt (locals_' x' !i)))"
  using rely_eq_queue[OF a1]  using a1 a2 a3 y 
    unfolding port_get_mutex_def  Let_def channel_get_mutex_def by fastforce
  have eq_locals:"locals_' x' !i = locals_' y'!i" using a3 y unfolding Rely_Send_ReceiveQ_def by auto
  have f1:"p_queuing conf (communication_' y') (pt (locals_' y' ! i))" 
    using a1 y a3 unfolding Rely_Send_ReceiveQ_def
    by (metis (no_types, lifting) a3 p_queuing_def port_channl_eq_ports rely_eq_ports)
  have f2:"port_get_mutex conf (communication_' y') (pt (locals_' y' ! i)) = Suc i"
    using a1 a2 a3 y 
    unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def port_get_mutex_def  
    channel_get_mutex_def Let_def eq_q
    by fastforce
  have f3:"channel_get_messages (the (chans (communication_' y') (port_channel conf (communication_' y') (pt (locals_' y' ! i))))) =
        B (port_channel conf (communication_' y') (pt (locals_' y' ! i))) + 
          channel_sent_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) adds (locals_' y') -
          channel_received_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) rems (locals_' y') + 
            {# msg (locals_' y' ! i) #} \<and>
         channel_received_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) rems  (locals_' y') \<subseteq>#
          B (port_channel conf (communication_' y') (pt (locals_' y' ! i))) + 
            channel_sent_messages (port_channel conf (communication_' y') (pt (locals_' y' ! i))) adds   (locals_' y') \<and>
      size (channel_get_messages  (the (chans (communication_' y') (port_channel conf (communication_' y') (pt (locals_' y' ! i))))))
        \<le> channel_size (get_channel conf (port_channel conf (communication_' y') (pt (locals_' y' ! i))))"
      using a4 a5 a6 eq_chan eq_q eq_locals port_chan
      unfolding  channel_received_messages_def channel_sent_messages_def 
        by auto
  then show "\<exists>y'. y = Normal y' \<and>
                   y' \<in> \<lbrace>p_queuing conf \<acute>communication (pt (\<acute>locals ! i))\<rbrace> \<inter> \<lbrace>port_get_mutex conf \<acute>communication (pt (\<acute>locals ! i)) = Suc i\<rbrace> \<inter>
                         \<lbrace>channel_get_messages (the (chans \<acute>communication (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))) =
                          add_mset (msg (\<acute>locals ! i))
                            (B (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) + 
                              channel_sent_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds \<acute>locals -
                              channel_received_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) rems \<acute>locals) \<and>
                           channel_received_messages (port_channel conf  \<acute>communication(pt (\<acute>locals ! i))) rems \<acute>locals  \<subseteq>#
                          B (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) +
                          channel_sent_messages (port_channel conf \<acute>communication (pt (\<acute>locals ! i))) adds \<acute>locals \<and>
                          size (channel_get_messages (the (chans \<acute>communication (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))))
                          \<le> channel_size (get_channel conf (port_channel conf \<acute>communication (pt (\<acute>locals ! i))))\<rbrace>"
   using y f1 f2 f3 by fastforce
qed
subsection {*Guarantee is in Rely*}
text{* we prove that Guarantee j is in Rely i for j!=i *}

lemma Guar_in_Rely_i1:
"i < n \<Longrightarrow>
 x < n \<Longrightarrow>
 x \<noteq> i \<Longrightarrow>
 a = Normal x1 \<Longrightarrow>
 b = Normal y1 \<Longrightarrow>
 \<forall>j<n. x \<noteq> j \<longrightarrow> locals_' x1 ! j = locals_' y1 ! j \<Longrightarrow>
  (locals_' x1)!i = (locals_' y1)!i"
by auto

lemma Guar_in_Rely_i2:
"i < n \<Longrightarrow>
 x < n \<Longrightarrow>
 x \<noteq> i \<Longrightarrow>
 a = Normal x1 \<Longrightarrow>
 b = Normal y1 \<Longrightarrow>
 \<forall>j<n. x \<noteq> j \<longrightarrow> locals_' x1 ! j = locals_' y1 ! j \<Longrightarrow>
 ports (communication_' x1) = ports (communication_' y1) \<Longrightarrow> 
 ports (communication_' x1) =  ports (communication_' y1)
"
by auto

lemma Guar_in_Rely_i3:
"x \<noteq> i \<Longrightarrow> 
 \<forall>j. j \<noteq> x \<longrightarrow> locals_' x1 ! j = locals_' y1 ! j \<Longrightarrow>   
  (a_que_aux (locals_' x1 !x) ch1 \<noteq> 
   a_que_aux (locals_' y1 !x) ch1 \<or>
   r_que_aux (locals_' x1 !x) ch1 \<noteq> 
   r_que_aux (locals_' y1 !x) ch1 \<longrightarrow>
    mut (the (chans (communication_' x1) ch1)) = x + 1 \<or>
    mut (the (chans (communication_' y1) ch1)) = x + 1 ) \<Longrightarrow>  
 (chans (communication_' x1) ch1\<noteq> 
  chans (communication_' y1) ch1 \<longrightarrow>
      mut (the (chans (communication_' x1) ch1)) = x + 1 \<or> 
      mut (the (chans (communication_' y1) ch1)) = x + 1 ) \<Longrightarrow>    
    (mut (the (chans (communication_' x1) ch1)) \<noteq>
     mut (the (chans (communication_' y1) ch1))) \<longrightarrow>
      (mut (the (chans (communication_' x1) ch1)) = 0 \<or> 
      mut (the (chans (communication_' y1) ch1)) = 0) \<Longrightarrow>  
  ((mut (the (chans (communication_' x1) ch1)) = i + 1 \<or> 
   mut (the (chans (communication_' y1) ch1)) = i + 1)  \<longrightarrow>
      chans (communication_' x1) ch1 =
      chans (communication_' y1) ch1 \<and>
      (\<forall>j. (a_que_aux (locals_' x1 !j) ch1) =  
                   (a_que_aux(locals_' y1 !j)) ch1 \<and>
                   (r_que_aux (locals_' x1 !j) ch1) =  
                   (r_que_aux(locals_' y1 !j)) ch1)                         
           )
"
proof(clarify)
  assume 
         a2:"x \<noteq> i" and                  
         a5:"\<forall>j. j \<noteq> x \<longrightarrow> locals_' x1 ! j = locals_' y1 ! j" and                             
         a9:"(chans (communication_' x1) ch1\<noteq> 
              chans (communication_' y1) ch1 \<longrightarrow>
                mut (the (chans (communication_' x1) ch1)) = x + 1 \<or> 
                mut (the (chans (communication_' y1) ch1)) = x + 1 )" and
         a10:"(mut (the (chans (communication_' x1) ch1)) \<noteq>
               mut (the (chans (communication_' y1) ch1))) \<longrightarrow>
                  (mut (the (chans (communication_' x1) ch1)) = 0 \<or> 
                   mut (the (chans (communication_' y1) ch1)) = 0)" and 
         a11:" a_que_aux (locals_' x1 ! x) ch1 \<noteq>
               a_que_aux (locals_' y1 ! x) ch1 \<or>
               r_que_aux (locals_' x1 ! x) ch1 \<noteq>
               r_que_aux (locals_' y1 ! x) ch1 \<longrightarrow>
                 mut (the (chans (communication_' x1) ch1)) = x + 1 \<or>
                 mut (the (chans (communication_' y1) ch1)) = x + 1 " and
         a12:"mut (the (chans (communication_' x1) ch1)) = i + 1 \<or>
              mut (the (chans (communication_' y1) ch1)) = i + 1"    
  have "chans (communication_' x1) ch1 = chans (communication_' y1) ch1"
    using   a2   a9 a10  a12 by force  
  also have "(\<forall>j. a_que_aux (locals_' x1 ! j) ch1 = a_que_aux (locals_' y1 ! j) ch1 \<and>
                    r_que_aux (locals_' x1 ! j) ch1 = r_que_aux (locals_' y1 ! j) ch1)"
    using  a2  a5 a11 a12 calculation by auto   
  ultimately show 
   "chans (communication_' x1) ch1 = chans (communication_' y1) ch1 \<and>
    (\<forall>j. a_que_aux (locals_' x1 ! j) ch1 = a_que_aux (locals_' y1 ! j) ch1 \<and>
          r_que_aux (locals_' x1 ! j) ch1 = r_que_aux (locals_' y1 ! j) ch1)" by auto
qed

 lemma guar_in_rely_i5:           
   assumes a0:"j\<noteq>i" and a0':"ch = port_channel conf (communication_' x) (pt (locals_' x !j))" and
     a1:"Guarantee_mod_chan x y j" and 
     a1':"ports (communication_' x) = ports (communication_' y)" and
    a2:"(chans (communication_' x) ch\<noteq> chans (communication_' y) ch \<longrightarrow>
          (mut (the (chans (communication_' x) ch)) = j + 1 \<or> 
           mut (the (chans (communication_' y) ch)) = j + 1))" and
    a3:"(\<forall>ch_id. ch_id\<noteq>ch \<longrightarrow>
            chans (communication_' x) ch_id = chans (communication_' y) ch_id)" and
    a4:" (\<forall>ch_id. (ch_id \<noteq> ch \<longrightarrow>
               (a_que_aux (locals_' x !j) ch_id = a_que_aux (locals_' y !j) ch_id) \<and> 
               (r_que_aux (locals_' x !j) ch_id = r_que_aux (locals_' y !j) ch_id)))" and
    a5:"\<forall>k. k\<noteq>j \<longrightarrow> locals_' x!k =locals_' y!k" and
    a6:"j<procs conf" 
  shows "Rely_mod_chan x y i"     
 proof-
   let ?ch_rel = "port_channel conf (communication_' x) (pt (locals_' x !i))"
  {
    assume eq_chan:"
      channel_get_messages (the (chans (communication_' x) ?ch_rel)) \<noteq>
      channel_get_messages (the (chans (communication_' y) ?ch_rel))" and
          p_queuing:"p_queuing conf (communication_' x) (pt (locals_' x !i))"          
   then have eq_port:"port_channel conf (communication_' x) (pt (locals_' x !i)) = 
                      port_channel conf (communication_' x) (pt (locals_' x !j))"
     using a3 a0' by auto 
   have p_q:"p_queuing conf  (communication_' x) (pt (locals_' x !j))" 
     using eq_port p_queuing p_queuing_def by auto       
   then have "
          port_open (communication_' x) (pt (locals_' x ! j)) \<and>
        (r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<or> 
         a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch) \<and>
       ((r_que_aux (locals_' y !j) ch\<noteq> r_que_aux (locals_' x !j) ch \<longrightarrow>
          (\<exists>m. r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch + m \<and>
             m\<subseteq># channel_get_messages (the (chans (communication_' x) ch)) \<and>
            channel_get_messages (the (chans (communication_' y) ch)) = 
              channel_get_messages (the (chans (communication_' x) ch)) - m) \<and>
            a_que_aux (locals_' x !j) ch = a_que_aux (locals_' y !j) ch) \<and>
        (a_que_aux (locals_' y !j) ch\<noteq> a_que_aux (locals_' x !j) ch \<longrightarrow>
         a_que_aux (locals_' y !j) ch = 
           {#msg (locals_' x !j)#} + a_que_aux (locals_' x !j) ch \<and>         
         r_que_aux (locals_' x !j) ch = r_que_aux (locals_' y !j) ch  \<and>
          size (channel_get_messages (the (chans (communication_' y) ch))) \<le> 
           channel_size (get_channel conf ch) \<and>
         channel_get_messages (the (chans (communication_' y) ch)) = 
           channel_get_messages (the (chans (communication_' x) ch)) +   
           {#msg (locals_' x !j)#} ) 
       )"
     using a1 eq_chan p_queuing eq_port p_q  a0'
     unfolding Guarantee_mod_chan_def Let_def by fastforce   
   note x = this[simplified a0' eq_port[THEN sym]]
   then have ?thesis using  eq_chan p_queuing a5 a4[simplified a0' eq_port[THEN sym]]  a6 a0' eq_port 
     unfolding Rely_mod_chan_def Let_def
     by blast                        
  } note l1 = this
  moreover {
    assume eq_chan:"(channel_get_messages (the (chans (communication_' x) ?ch_rel)) =
       channel_get_messages (the (chans (communication_' y) ?ch_rel))) \<or>
             \<not> (p_queuing conf (communication_' x) (pt (locals_' x !i)))"   
      {assume eq_chann:"(channel_get_messages (the (chans (communication_' x) ?ch_rel)) =
             channel_get_messages (the (chans (communication_' y) ?ch_rel)))"
        {assume eq_port:"?ch_rel = ch"
         then have "r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
          a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch" 
         using a1 eq_chan eq_chann a0'   unfolding Guarantee_mod_chan_def Let_def by auto         
       then have ?thesis using a5 eq_chann eq_port   
         unfolding Rely_mod_chan_def Let_def by fastforce          
        }   
        moreover{assume eq_port:"?ch_rel \<noteq> ch"            
           then have ?thesis using a5 eq_chann eq_port a0' unfolding Rely_mod_chan_def Let_def
             by (metis a4) 
        }     
        ultimately have "?thesis" by auto
      }
      moreover 
      {assume not_pque:"\<not> p_queuing conf (communication_' x) (pt (locals_' x !i))"
        {assume eq_port:"?ch_rel = ch"
           then have "r_que_aux (locals_' y !j) ch = r_que_aux (locals_' x !j) ch \<and>
            a_que_aux (locals_' y !j) ch = a_que_aux (locals_' x !j) ch" 
             using a1 eq_chan not_pque a0' 
             unfolding Guarantee_mod_chan_def Let_def p_queuing_def by auto            
         then have ?thesis using a5 eq_port not_pque a0' 
           unfolding Rely_mod_chan_def Let_def by fastforce           
         }   
         moreover{
           assume eq_port:"?ch_rel \<noteq> ch"            
           then have ?thesis using a5 not_pque eq_port a0' 
             unfolding Rely_mod_chan_def Let_def by (metis a4) 
        }     
        ultimately have "?thesis" by auto         
     }
     ultimately have ?thesis using eq_chan by auto
  }ultimately show ?thesis by auto     
qed  
  
lemma Guar_in_Rely_i4:
"i < n \<Longrightarrow>
 x < n \<Longrightarrow>
 x \<noteq> i \<Longrightarrow>
 a = Normal x1 \<Longrightarrow>
 b = Normal y1 \<Longrightarrow>
 \<forall>j. j \<noteq> x \<longrightarrow> locals_' x1 ! j = locals_' y1 ! j \<Longrightarrow> 
 (\<forall>ch. ch \<noteq> ch1 \<longrightarrow>
      chans (communication_' x1) ch = chans (communication_' y1) ch) \<Longrightarrow>
 ((\<exists>ch. chans (communication_' x1) ch1 =  Some ch \<and> chan_queuing ch) \<longrightarrow>
  (\<exists>ch. chans (communication_' y1) ch1 =  Some ch \<and> chan_queuing ch)) \<Longrightarrow>
 (\<forall>ch_id.
     ((\<exists>ch. chans (communication_' x1) ch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
      (\<exists>ch. chans (communication_' y1) ch_id =  Some ch \<and> chan_queuing ch)))"
  by metis
 
  
lemma Guar_Rely_Send_ReceiveQ1:
"i < n \<Longrightarrow> 
 x < n \<Longrightarrow> x \<noteq> i \<Longrightarrow>
 procs conf = n \<Longrightarrow>
 (a, b) \<in> Guarantee_Send_Receive x  \<Longrightarrow> a=b \<Longrightarrow>
 (a, b) \<in> Rely_Send_ReceiveQ i"
  unfolding Guarantee_Send_Receive_def Rely_Send_ReceiveQ_def by auto

lemma Guar_Rely_Send_ReceiveQ2:
"i < n \<Longrightarrow> 
 x < n \<Longrightarrow> x \<noteq> i \<Longrightarrow>
 procs conf = n \<Longrightarrow>
 (a, b) \<in> Guarantee_Send_Receive x  \<Longrightarrow> a\<noteq>b \<Longrightarrow>
 (a, b) \<in> Rely_Send_ReceiveQ i" 
  proof-
  assume a0:"i<n" and
         a1:"x<n" and
         a2:"x\<noteq>i" and a2':" procs conf = n" and
         a3:"(a,b) \<in> Guarantee_Send_Receive x" and a4:"a\<noteq>b"
 then obtain x1 y1 where
a3a:"a = Normal x1" and
 a3b:"b = Normal y1" and
  a30:"length (locals_' x1) = length (locals_' y1)" and   
  a3':"evnt (locals_' x1 !x) = evnt (locals_' y1 !x) \<and> 
       pt (locals_' x1 !x) =  pt (locals_' y1 !x) \<and>
       state_conf x1 = state_conf y1" and
  a3c: "(\<forall>j. (j\<noteq>x) \<longrightarrow> (locals_' x1)!j = (locals_' y1)!j)"
   unfolding Guarantee_Send_Receive_def by fastforce     
  then have a3'':"(x1,y1)\<in> Guarantee_Send_Receive' x"
    using  a3 a4 unfolding Guarantee_Send_Receive_def by auto
  note g1 = case_prodD[OF CollectD[OF a3''[simplified Guarantee_Send_Receive'_def Let_def]]]
  then have
  g1:"(\<forall>ch_id. ch_id\<noteq>(port_channel conf (communication_' x1) (pt (locals_' x1 !x))) \<longrightarrow>
            chans (communication_' x1) ch_id = chans (communication_' y1) ch_id \<and>
            (a_que_aux (locals_' x1 !x) ch_id = a_que_aux (locals_' y1 !x) ch_id) \<and> 
               (r_que_aux (locals_' x1 !x) ch_id = r_que_aux (locals_' y1 !x) ch_id))" and     
  g2:" schedule (locals_' x1 !x) =  schedule (locals_' y1 !x) \<and>      
     (\<forall>ch_id. (ch_id \<noteq> (port_channel conf (communication_' x1) (pt (locals_' x1 !x))) \<longrightarrow>
               (a_que_aux (locals_' x1 !x) ch_id = a_que_aux (locals_' y1 !x) ch_id) \<and> 
               (r_que_aux (locals_' x1 !x) ch_id = r_que_aux (locals_' y1 !x) ch_id))) \<and>
    ((a_que_aux (locals_' x1 !x) \<noteq> a_que_aux (locals_' y1 !x) \<or> 
     (r_que_aux (locals_' x1 !x) \<noteq> r_que_aux (locals_' y1 !x))) \<longrightarrow>
      (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1 \<or>
       mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1)
    ) \<and>
    (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x)))\<noteq> 
    chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))) \<longrightarrow>
      (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1 \<or> 
       mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = x + 1)) \<and> 
   (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) \<noteq>
    mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) \<longrightarrow>
      (mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = 0 \<or> 
      mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !x))))) = 0))" 
    unfolding Guarantee_Send_Receive'_def Let_def
    by auto 
     
   have"ports (communication_' x1) = ports (communication_' y1) \<and>
   ({ch. chans (communication_' x1) ch = None} = 
      {ch. chans (communication_' y1) ch = None}) \<and>
    ({ch. \<exists>ch1. chans (communication_' x1) ch = Some ch1} = 
      {ch. \<exists>ch1. chans (communication_' y1) ch = Some ch1})"    
    using  a3'' unfolding Guarantee_Send_Receive'_def Let_def
    by clarify
   moreover have eq_port_channel:"(port_channel conf (communication_' x1) (pt (locals_' x1 !x))) =
                         (port_channel conf (communication_' y1) (pt (locals_' x1 !x)))"
   using calculation by (simp add: port_channl_eq_ports)
   moreover have 
    "(\<forall>ch_id.
      ((\<exists>ch. chans (communication_' x1) ch_id =  Some ch \<and> chan_queuing ch) \<longrightarrow>
      (\<exists>ch. chans (communication_' y1) ch_id =  Some ch \<and> chan_queuing ch)))"
    using a3 a3' a3'' Guar_in_Rely_i4[OF a0 a1 a2 a3a a3b a3c] 
    unfolding Guarantee_Send_Receive'_def Let_def by auto
  moreover have "((mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = i + 1 \<or> 
   mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))))) = i + 1)  \<longrightarrow>
      chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) =
      chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) \<and>
      (\<forall>j. (a_que_aux (locals_' x1 !j) (port_channel conf (communication_' x1) (pt (locals_' x1 !i)))) =  
                   (a_que_aux(locals_' y1 !j)) (port_channel conf (communication_' x1) (pt (locals_' x1 !i))) \<and>
                   (r_que_aux (locals_' x1 !j) (port_channel conf (communication_' x1) (pt (locals_'  x1 !i)))) =  
                   (r_que_aux(locals_' y1 !j)) (port_channel conf (communication_' x1) (pt (locals_'  x1 !i))))                         
           )
   " using g1 g2  Guar_in_Rely_i3[OF a2 a3c _ _ _, of "(port_channel conf (communication_' x1) (pt (locals_' x1 ! i)))"] 
    
  proof-
    have a0:"a_que_aux (locals_' x1 ! x) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<noteq>
    a_que_aux (locals_' y1 ! x) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<or>
    r_que_aux (locals_' x1 ! x) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<noteq>
    r_que_aux (locals_' y1 ! x) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<longrightarrow>
    mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = x + 1 \<or>
    mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) =
    x + 1" using  g2  by metis
    have a1:"chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<noteq>
    chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))) \<longrightarrow>
    mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = x + 1 \<or>
    mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) =
    x + 1" using  g1 g2 by metis
    have a3:" mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
  mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<longrightarrow>
  mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = 0 \<or>
  mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) = 0"
      using g1 g2 by metis
    show ?thesis      
      using Guar_in_Rely_i3[OF a2 a3c a0 a1 a3] by fastforce
  qed     
  moreover have "(\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) \<longrightarrow> 
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id)"
    using a3'' a1 a2'  unfolding Guarantee_Send_Receive'_def Let_def by blast              
  moreover have "(\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x1) (pt (locals_' x1 !j))) \<longrightarrow> 
      chans (communication_' x1) ch_id = chans (communication_' y1) ch_id \<and> 
     (\<forall>i.(a_que_aux (locals_' x1 !i) ch_id = a_que_aux (locals_' y1 !i) ch_id) \<and> 
         (r_que_aux (locals_' x1 !i) ch_id = r_que_aux (locals_' y1 !i) ch_id) ))"
    using a1 a2' a3c g1 by force          
  moreover have G:"Guarantee_mod_chan x1  y1 x" using a3'' 
    unfolding Guarantee_Send_Receive'_def Let_def
    by clarsimp
  then have "Rely_mod_chan x1 y1 i" using guar_in_rely_i5[OF a2 _  G _ _ _ _ a3c] g1 g2
    by (simp add: a1 a2' calculation(1) eq_port_channel)    
  moreover have 
    "(mut (the (chans (communication_' x1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
         i + 1 \<longrightarrow>
     mut (the (chans (communication_' y1) (port_channel conf (communication_' x1) (pt (locals_' x1 ! i))))) \<noteq>
     i + 1)"
    using calculation by fastforce     
  ultimately have "(x1,y1)\<in>Rely_Send_Receive i"
    unfolding Rely_Send_Receive_def Let_def by fastforce  
  thus ?thesis using a2 a3a a3b a30 a3' a3c   unfolding Rely_Send_ReceiveQ_def
   by auto
qed

lemma Guar_Rely_Send_ReceiveQ:
"i < n \<Longrightarrow> 
 x < n \<Longrightarrow> x \<noteq> i \<Longrightarrow>
 procs conf = n \<Longrightarrow>
 (a, b) \<in> Guarantee_Send_Receive x  \<Longrightarrow> 
 (a, b) \<in> Rely_Send_ReceiveQ i"
  using Guar_Rely_Send_ReceiveQ1 Guar_Rely_Send_ReceiveQ2 by fastforce

definition Rely_System
where 
"Rely_System \<equiv> {(x,y). (\<exists>x1 y1. x=Normal x1 \<and> y=Normal y1 \<and> 
                     locals_' x1 = locals_' y1 \<and> 
                     communication_' x1 = communication_' y1)}
"


section {* Property Definitions *}

  
definition Invariant 
where
"Invariant B adds rems i \<equiv>                                         
  {s. state_conf s}   \<inter> {s. channel_spec B adds rems (port_channel conf (communication_' s) (pt (locals_' s !i))) s}
"  

definition Invariant_mut
where
"Invariant_mut B adds rems i \<equiv>                                         
  {s. state_conf s}   \<inter> {s. channel_spec_mut B adds rems (port_channel conf (communication_' s) (pt (locals_' s !i))) s}
"  

lemma procs_len_locals:"i< procs conf \<Longrightarrow>    
      x\<in> Invariant B adds rems i \<Longrightarrow>
     i< length (locals_' x)"
  unfolding Invariant_def state_conf_def by auto
 
lemma Invariant_eq:  
    "chans (communication_' x1) =chans(communication_' y1) \<Longrightarrow>
     ports (communication_' x1) = ports(communication_' y1) \<Longrightarrow>
     (x1,y1,i) \<in> preserves_locals_constr  \<Longrightarrow>
     a_que_aux ((locals_' x1)!i)  = a_que_aux ((locals_' y1)!i)  \<Longrightarrow>
     r_que_aux ((locals_' x1)!i)  = r_que_aux ((locals_' y1)!i) \<Longrightarrow>
     x1\<in> Invariant B adds rems i \<Longrightarrow>
     y1\<in> Invariant B adds rems i"
  unfolding Invariant_def 
     apply (frule port_channl_eq_ports[of _ _ i])  
   unfolding   state_conf_def port_exists_def                                     
   by (simp add: preserves_locals_D1 channel_spec_eq preserves_locals_D3 
          add_channel_message_not_evnt)+         
        
    
definition pre_i 
where
"pre_i B adds rems i  \<equiv>
  Invariant B adds rems i"
                      
definition pre_send 
where
"pre_send B adds rems i \<equiv> pre_i B adds rems i  \<inter> \<lbrace>evnt (\<acute>locals!i) = Send_Message_Q \<rbrace>"
(* remove for Case-Study
definition pre_receive
where
"pre_receive B i \<equiv> pre_i B i \<inter> \<lbrace>evnt (\<acute>locals!i) = Receive_Message_Q \<rbrace>"

*) 

definition chans_spec
where
"chans_spec B adds rems \<equiv>
  {s.  \<forall>ch_id. 
     channel_spec B adds rems ch_id s }
"


definition Post_Send
where
"Post_Send B adds rems i \<equiv> Invariant B adds rems i \<inter> 
                 \<lbrace>(ret_n ((\<acute>locals)!i)) = 1 \<and>                        
                      {# (msg ((\<acute>locals)!i)) #} \<subseteq># 
                  a_que_aux (\<acute>locals!i) (port_channel conf \<acute>communication (pt (\<acute>locals !i))) \<rbrace>
"

definition Post_Receive
where
"Post_Receive B adds rems i \<equiv> 
  {s. s\<in>Invariant B adds rems i}  \<inter> 
  \<lbrace>(ret_n ((\<acute>locals)!i)) = 1 \<longrightarrow>                      
    (port_open (\<acute>communication)  ((pt ((\<acute>locals)!i)))) \<and> 
    the (ret_msg ((\<acute>locals)!i)) \<in># 
     (B (port_channel conf \<acute>communication (pt ((\<acute>locals)!i))) +                 
        channel_sent_messages (port_channel conf \<acute>communication (pt ((\<acute>locals)!i))) adds \<acute>locals) 
  \<rbrace>
"

definition Post_Arinc_i
where                
"Post_Arinc_i B adds rems i \<equiv> Invariant B adds rems i
"

definition Post_Arinc_i_mut
where                
"Post_Arinc_i_mut B adds rems i \<equiv> Invariant_mut B adds rems i
"
 
definition Post_Arinc
where                
"Post_Arinc B adds rems i \<equiv> Invariant B adds rems i
"

definition Inv_QueCom_ch
where
"Inv_QueCom_ch B adds rems ch_id  \<equiv> 
    {s. state_conf s   \<and> channel_spec B adds rems ch_id s}"  

definition Pre_QueCom_ch
  where
    "Pre_QueCom_ch B adds rems ch_id  \<equiv>   
   {s. state_conf s} \<inter> {s. (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' s) (pt (locals_' s !j))) \<longrightarrow>
       s\<in>Inv_QueCom_ch B adds rems ch_id }"
    
definition Inv_QueCom
where
"Inv_QueCom B adds rems  \<equiv> {s. state_conf s}   \<inter> {s. \<forall>ch_id. channel_spec B adds rems ch_id s} " 

definition Inv_QueCom_ch_mut
where
"Inv_QueCom_ch_mut B adds rems ch_id  \<equiv> 
    {s. state_conf s   \<and> channel_spec_mut B adds rems ch_id s}"  

definition Pre_QueCom_ch_mut
  where
    "Pre_QueCom_ch_mut B adds rems ch_id  \<equiv>   
   {s. state_conf s} \<inter> {s. (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' s) (pt (locals_' s !j))) \<longrightarrow>
       s\<in>Inv_QueCom_ch_mut B adds rems ch_id }"
    
definition Inv_QueCom_mut
where
"Inv_QueCom_mut B adds rems  \<equiv> {s. state_conf s}   \<inter> {s. \<forall>ch_id. channel_spec_mut B adds rems ch_id s}" 

subsection {* lemmas on stability and reflexivity of Rely\_Send*}

lemma eq_locals:
 "length (locals_' x) = length (locals_' y) \<Longrightarrow>
  \<forall>i<length (locals_' x). msgc (locals_' x !i) ch_id = msgc (locals_' y !i) ch_id \<Longrightarrow>
  channel_messages  ch_id msgc (locals_' x)  =
  channel_messages  ch_id msgc  (locals_' y) "  
  by (metis same_channel_messages)
      
lemma rely_state_conf:
  assumes a1:"(Normal x', Normal y') \<in> Rely_Send_ReceiveQ i" and
          a2:"state_conf x'" 
        shows"state_conf y'"
  using  a1 a2 unfolding state_conf_def Rely_Send_ReceiveQ_def  by auto
    
lemma sta_invariant_rely_send:       
 "i<procs conf \<Longrightarrow> Sta (Invariant B adds rems i) (Rely_Send_ReceiveQ i)"
unfolding Invariant_def Sta_def 
proof clarify  
  fix y x'    
  let ?ch_id = "port_channel conf (communication_' (x'::'a vars_scheme)) (pt (locals_' x' ! i))"
  assume a0':"i< procs conf" and a0: "state_conf x'" and         
         a2:"channel_spec B adds rems  ?ch_id x'" and
         a3:"(Normal x', (y::('a vars_scheme, 'b) xstate)) \<in> Rely_Send_ReceiveQ i"   
  then obtain y' where y:"y=Normal y'" 
    unfolding Rely_Send_ReceiveQ_def by auto 
  have i_len:"i<length (locals_' x')" 
    using a0 a0' a2 procs_len_locals unfolding state_conf_def by fastforce   
  have procs_len:"procs conf = length (locals_' x')"
        using a0 a0' a2 procs_len_locals unfolding state_conf_def by fastforce
  have len:"length (locals_' x') = length (locals_' y')" 
    using y a3 unfolding Rely_Send_ReceiveQ_def by auto
  have pt:"pt ((locals_' x')!i) = pt ((locals_' y')!i)"
    using y a3 unfolding Rely_Send_ReceiveQ_def by auto
  have eq_port:"?ch_id  = port_channel conf (communication_' y') (pt (locals_' x' ! i))"
    using a3 y port_channl_eq_ports unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def
    by auto             
  have "channel_spec B adds rems (port_channel conf (communication_' y') (pt (locals_' y' ! i))) y'"
  proof-
    { 
    fix ch'
    assume ass01: "chans (communication_' y') (port_channel conf (communication_' y') (pt (locals_' y' ! i))) = Some ch' \<and>
            ch_id_queuing conf (port_channel conf (communication_' y') (pt (locals_' y' ! i)))"
    then obtain ch where
    assx:"chans (communication_' x') ?ch_id = Some ch \<and>
               ch_id_queuing conf ?ch_id"
      using ch_id_queuing[OF a0 ass01[simplified pt[THEN sym] eq_port[THEN sym]]] by auto
     then have p_q:"p_queuing conf (communication_' x') (pt (locals_' x' ! i))"
       unfolding p_queuing_def by auto  
     then have spec_x1:"channel_get_messages ch = B ?ch_id +
       channel_sent_messages ?ch_id adds (locals_' x') -
       channel_received_messages ?ch_id rems (locals_' x')" and
       spec_x2:"channel_received_messages ?ch_id rems (locals_' x') \<subseteq># B ?ch_id +
          channel_sent_messages ?ch_id adds (locals_' x')" and
       spec_x3:"(size (channel_get_messages ch) \<le> channel_size (get_channel conf ?ch_id))" and
       spec_x4: "channel_messages ?ch_id rems [0..<length (locals_' x')] \<subseteq># 
                   channel_messages  ?ch_id r_que_aux (locals_' x')" and
        spec_x5: "channel_messages ?ch_id adds [0..<length (locals_' x')] \<subseteq># 
                   channel_messages  ?ch_id a_que_aux (locals_' x')"
       using assx a2 ass01  unfolding channel_spec_def ch_spec_def by auto
     then have ?thesis unfolding channel_spec_def ch_spec_def using
        Rely_chan_spec    y assx pt  a3 p_q procs_len Rely_chan_eq
       by (metis (no_types) option.sel)           
   
   } thus ?thesis using channel_spec_intro by blast
 qed  
  then show "\<exists>y'. y = Normal y' \<and>
            y' \<in> Collect state_conf  \<inter>
            {s. channel_spec B adds rems (port_channel conf (communication_' s) (pt (locals_' s ! i))) s} " 
    using a0 a3 y rely_state_conf by blast
qed


 lemma pre_state_com:
   "\<forall>ch_id. ch_id\<noteq> ch \<longrightarrow>
      chans (communication_' s) ch_id  = chans (communication_' s') ch_id  \<Longrightarrow> 
    (chans (communication_' s) ch \<noteq> chans (communication_' s') ch) \<longrightarrow>
     (\<forall>chs. chans (communication_' s) ch = Some chs \<longrightarrow>
       (\<exists>chs'. chans (communication_' s') ch = Some chs' \<and> chan_queuing chs = chan_queuing chs')) \<Longrightarrow>
    ports (communication_' s) = ports (communication_' s')  \<Longrightarrow>
   length (locals_' s) =  length (locals_' s') \<Longrightarrow>   
    state_conf s \<Longrightarrow>
    state_conf  s'"    
  unfolding  state_conf_def port_exists_def
  apply auto
     apply metis
    apply(case_tac "(channel_id cha) = ch")
    by auto
    
    
lemma pre_quecom_ch:
  assumes 
  a0:"i< procs conf" and
  a1:"ch = port_channel conf (communication_' s) (pt(locals_' s!i))" and
  a2:"\<forall>ch_id. ch_id\<noteq> ch \<longrightarrow>
      chans (communication_' s) ch_id  = chans (communication_' s') ch_id" and
  a3:"(chans (communication_' s) ch \<noteq> chans (communication_' s') ch) \<longrightarrow>
     (\<forall>chs. chans (communication_' s) ch = Some chs \<longrightarrow>
       (\<exists>chs'. chans (communication_' s') ch = Some chs' \<and> chan_queuing chs = chan_queuing chs'))" and
  a4:"ports (communication_' s) = ports (communication_' s') " and
  a5:"length (locals_' s) =  length (locals_' s')" and
  a6:"\<forall>i. pt (locals_' s ! i) = pt (locals_' s' ! i)" and
  a7:"(\<forall>i.(a_que_aux (locals_' s !i) ch_id = a_que_aux (locals_' s' !i) ch_id) \<and> 
       (r_que_aux (locals_' s !i) ch_id = r_que_aux (locals_' s' !i) ch_id) )" and
  a8:"s\<in>Pre_QueCom_ch B adds rems ch_id"
  shows"s'\<in>Pre_QueCom_ch B adds rems ch_id"    
proof-
  have "state_conf s'" 
    using a8 pre_state_com[OF a2 a3 a4 a5] unfolding Pre_QueCom_ch_def by auto
  moreover 
  {assume 
     b0:"(\<nexists>j. j<procs conf \<and> ch_id = port_channel  conf (communication_' s') (pt (locals_' s' !j)))"     
    then have "s\<in>Inv_QueCom_ch B adds rems ch_id" 
      using port_channl_eq_ports[OF a4] a8 a6 unfolding Pre_QueCom_ch_def
      by auto
    then have "s'\<in>Inv_QueCom_ch B adds rems ch_id"       
      using port_channl_eq_ports[OF a4]
      unfolding Inv_QueCom_ch_def   
      by (metis (lifting)  a0 a1 a2 a5 a6 a7 b0 calculation ch_spec_def channel_received_messages_def 
         channel_sent_messages_def channel_spec_dest2
        channel_spec_intro mem_Collect_eq same_message_channel) 
  }  
  ultimately show ?thesis unfolding Pre_QueCom_ch_def by fastforce
 qed
   
lemma pre_quecom_ch':
  assumes 
  a0:"i< procs conf" and
  a1:"ch = port_channel conf (communication_' s) (pt(locals_' s!i))" and
  a2:"\<forall>ch_id. ch_id\<noteq> ch \<longrightarrow>
      chans (communication_' s) ch_id  = chans (communication_' s') ch_id" and
  a3:"(chans (communication_' s) ch \<noteq> chans (communication_' s') ch) \<longrightarrow>
     (\<forall>chs. chans (communication_' s) ch = Some chs \<longrightarrow>
       (\<exists>chs'. chans (communication_' s') ch = Some chs' \<and> chan_queuing chs = chan_queuing chs'))" and
  a4:"ports (communication_' s) = ports (communication_' s') " and
  a5:"length (locals_' s) =  length (locals_' s')" and
  a6:"\<forall>i. pt (locals_' s ! i) = pt (locals_' s' ! i)" and
  a7:"(\<forall>j. j\<noteq>i \<longrightarrow> (a_que_aux (locals_' s !j)  = a_que_aux (locals_' s' !j)) \<and> 
                    (r_que_aux (locals_' s !j)  = r_que_aux (locals_' s' !j) ) )" and   
  a7':"(\<forall>j. j\<noteq> ch \<longrightarrow> 
            a_que_aux ((locals_' s)!i) j = a_que_aux ((locals_' s')!i) j \<and>
            r_que_aux ((locals_' s)!i) j = r_que_aux ((locals_' s')!i) j)" and
  a8:"s\<in>Pre_QueCom_ch B adds rems ch_id"
  shows"s'\<in>Pre_QueCom_ch B adds rems ch_id"    
proof-
  have state:"state_conf s'" 
    using a8 pre_state_com[OF a2 a3 a4 a5] unfolding Pre_QueCom_ch_def by auto
  moreover 
  {assume 
     b0:"(\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' s') (pt (locals_' s' !j)))"
    then have b0':"\<forall>j. j\<ge>procs conf \<or> ch_id\<noteq>port_channel conf (communication_' s') (pt (locals_' s' !j))"
      using leI by auto 
        then have a7:"\<forall>i. (a_que_aux (locals_' s' !i) ch_id = a_que_aux (locals_' s !i) ch_id) \<and>
                         (r_que_aux (locals_' s' !i) ch_id = r_que_aux (locals_' s !i) ch_id)"
          using a7 a7' a6 port_channl_eq_ports[OF a4] a1 by (metis a0 b0) 
        then have "s\<in>Inv_QueCom_ch B adds rems ch_id" using a8 a6 b0 port_channl_eq_ports[OF a4]
          unfolding Pre_QueCom_ch_def
          by auto                 
        then have "s'\<in>Inv_QueCom_ch B adds rems ch_id"       
          unfolding Inv_QueCom_ch_def using port_channl_eq_ports[OF a4]
        by (metis (lifting)  a0 a1 a2 a5 a6 a7  b0 state ch_spec_def channel_received_messages_def 
           channel_sent_messages_def channel_spec_dest2 
          channel_spec_intro mem_Collect_eq same_message_channel)
   } ultimately show ?thesis unfolding Pre_QueCom_ch_def by auto
 qed   
   
lemma sta_no_channel_rely_send:
  " i < procs conf \<Longrightarrow>
    Sta (Pre_QueCom_ch B adds rems ch_id) (Rely_Send_ReceiveQ i)"  
  unfolding Sta_def 
proof clarsimp   
   fix x'::"'a vars_scheme" and y::"('a vars_scheme, 'b) xstate"
   assume a0:"i < Sys_Config.procs conf" and
           a1:"x' \<in> Pre_QueCom_ch B adds rems ch_id" and
           a2:"(Normal x', y) \<in> Rely_Send_ReceiveQ i"
   then obtain y' where y:"y = Normal y'" unfolding Rely_Send_ReceiveQ_def by auto
   then have eq_ports: "ports (communication_' x') = ports (communication_' y')" 
    using a2 unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by auto
   have state_conf_y:"state_conf y'" 
   proof-{
       show ?thesis using a2 a1 y unfolding Pre_QueCom_ch_def 
           by (fastforce simp: rely_state_conf)
   } qed
   moreover{
     assume a3:"(\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' y') (pt (locals_' y' !j)))"  
     then have "(\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' x') (pt (locals_' x' !j)))" 
       using y a2 port_channl_eq_ports[OF eq_ports] 
       unfolding Rely_Send_ReceiveQ_def
       by auto
     then have eq_vars:"
      chans (communication_' x') ch_id = chans (communication_' y') ch_id \<and>
       (\<forall>i.(a_que_aux (locals_' x' !i) ch_id = a_que_aux (locals_' y' !i) ch_id) \<and> 
           (r_que_aux (locals_' x' !i) ch_id = r_que_aux (locals_' y' !i) ch_id) )"
       using a2 y port_channl_eq_ports[OF eq_ports] 
       unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Let_def by blast    
     moreover have x_inv:"x'\<in> Inv_QueCom_ch B adds rems ch_id" 
       using a1 a2 y a3 port_channl_eq_ports[OF eq_ports]  
       unfolding Pre_QueCom_ch_def Rely_Send_ReceiveQ_def by auto
     moreover have "length (locals_' y') = length (locals_' x')"
       using  a1 state_conf_y 
       unfolding  Pre_QueCom_ch_def state_conf_def by auto
     ultimately have "y'\<in>Inv_QueCom_ch B adds rems ch_id"        
       using  same_message_channel unfolding Inv_QueCom_ch_def
          by (metis (no_types, lifting) a2 ch_spec_def 
                    channel_received_messages_def channel_sent_messages_def 
                    channel_spec_def eq_vars mem_Collect_eq rely_state_conf y)
   }
   ultimately show "\<exists>y'. y = Normal y' \<and> y' \<in> Pre_QueCom_ch B adds rems ch_id" 
     unfolding Pre_QueCom_ch_def
     using y by auto 
 qed
   
 definition post_1_i
where                
"post_1_i B adds rems \<equiv> 
    \<lbrace>\<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf \<acute>communication (pt (\<acute>locals !j))) \<longrightarrow> 
      chans (\<acute>communication) ch_id = B ch_id \<and> 
     (\<forall>i.(a_que_aux (\<acute>locals !i) ch_id = adds i ch_id) \<and> 
         (r_que_aux (\<acute>locals !i) ch_id = rems i ch_id) )\<rbrace>"    

definition post_1_i_s
where                
"post_1_i_s s B adds rems \<equiv> 
    \<forall>ch_id. 
      (\<nexists>j. j<procs conf \<and> ch_id = port_channel conf (communication_' s) (pt (locals_' s !j))) \<longrightarrow> 
      chans (communication_' s) ch_id = B ch_id \<and> 
     (\<forall>i.(a_que_aux (locals_' s !i) ch_id = adds i ch_id) \<and> 
         (r_que_aux (locals_' s !i) ch_id = rems i ch_id))"


 subsection {* Stability *} 
lemma sta_uni:"LocalRG_HoareDef.Sta UNIV (Rely_Send_ReceiveQ i)"
  unfolding Sta_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def by blast
    
lemma stable_state_conf:"i < Sys_Config.procs conf \<Longrightarrow>      
      LocalRG_HoareDef.Sta {s. state_conf s}  (Rely_Send_ReceiveQ i)"
  unfolding state_conf_def Rely_Send_ReceiveQ_def Sta_def
  by fastforce
  
lemma stable_post:"i < Sys_Config.procs conf \<Longrightarrow>      
      LocalRG_HoareDef.Sta {s. post_1_i_s s B adds rems}  (Rely_Send_ReceiveQ i)"  
  unfolding post_1_i_s_def Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def Let_def
    port_channel_def port_in_channel_def port_name_in_channel_def port_id_name_def port_exists_def
    by fastforce
      
lemma stable_state:"i < Sys_Config.procs conf \<Longrightarrow>      
      LocalRG_HoareDef.Sta ({s. state_conf s} \<inter> {s. post_1_i_s s B adds rems}) 
  (Rely_Send_ReceiveQ i)"
  using stable_state_conf stable_post by (fastforce intro:Sta_intro)
 
    lemma sta_event:"LocalRG_HoareDef.Sta (\<lbrace>evnt (\<acute>locals ! i) = x\<rbrace>) (Rely_Send_ReceiveQ i)"
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def
  by fastforce
    
lemma sta_event_inv:
  "i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta (Invariant B adds rems i \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace>) (Rely_Send_ReceiveQ i) "   
  using sta_event sta_invariant_rely_send by (fastforce intro:Sta_intro)  
    
lemma sta_event_inv_PreQue:
  "i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta (Pre_QueCom_ch B adds rems ch_id \<inter> \<lbrace>evnt (\<acute>locals ! i) = x\<rbrace>) (Rely_Send_ReceiveQ i) "   
  using sta_event sta_no_channel_rely_send by (fastforce intro:Sta_intro)
  
lemma sta_not_event:"LocalRG_HoareDef.Sta (-\<lbrace>evnt (\<acute>locals ! i) = x\<rbrace>) (Rely_Send_ReceiveQ i)"
  unfolding Rely_Send_ReceiveQ_def Rely_Send_Receive_def Sta_def
  by fastforce        
    
lemma sta_not_event_inv:
  "i < Sys_Config.procs conf \<Longrightarrow>
    LocalRG_HoareDef.Sta (Invariant B adds rems i \<inter> -\<lbrace>evnt (\<acute>locals ! i) = x\<rbrace>) (Rely_Send_ReceiveQ i) "   
   using sta_not_event sta_invariant_rely_send by (fastforce intro:Sta_intro)
    
end
  
