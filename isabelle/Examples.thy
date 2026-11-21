theory Examples
  imports Main_Results
begin

section \<open>Examples\<close>

text \<open>
  Variables are natural numbers: \<open>x = 0\<close>, \<open>y = 1\<close>, and so on.
  Reduction is call-by-value \<open>\<rightarrow>\<^sub>v\<close>: the union of \<open>\<sigma>\<close> and \<open>\<beta>\<^sub>v\<close>.
\<close>

subsection \<open>Helpers\<close>

text \<open>A term that reduces to a normal fireball is typable.\<close>

lemma ex_Typ_of_reduct:
  assumes "M \<rightarrow>\<^sub>v\<^sup>* N" "NF N" "fb N"
  shows "Typ M"
proof -
  have "CFN M" unfolding CFN_def using assms by blast
  then show ?thesis using main_characterization by blast
qed

text \<open>A term with no \<open>\<sigma>\<close>-step and no \<open>\<beta>\<^sub>v\<close>-step is a normal form.\<close>

lemma ex_NF_intro:
  assumes s: "\<And>Q. \<not> M \<rightarrow>\<^sub>\<sigma> Q" and b: "\<And>Q. \<not> M \<rightarrow>\<^sub>\<beta> Q"
  shows "NF M"
proof (rule normalI)
  fix Q
  show "\<not> M \<rightarrow>\<^sub>v Q" using s[of Q] b[of Q] unfolding cbv_def by blast
qed

lemma ex_no_sig_Id: "Id \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> False" by (auto elim: sig.cases)
lemma ex_no_sig_Var: "Var x \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> False" by (auto elim: sig.cases)
lemma ex_no_sig_Nm: "Nm x \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> False" by (auto elim: sig.cases)

lemma ex_NF_Id: "NF Id"
  by (rule ex_NF_intro) (auto elim!: sig.cases beta.cases dest: ex_no_sig_Id Id_no_beta)

lemma ex_NF_App_Id_Var: "NF (App Id (Var 1))"
  by (rule ex_NF_intro)
    (auto elim!: sig.cases beta.cases dest: ex_no_sig_Id ex_no_sig_Var Id_no_beta Var_no_beta)

lemma ex_NF_App_Nm_Var: "NF (App (Nm 0) (Var 1))"
  by (rule ex_NF_intro)
    (auto elim!: sig.cases beta.cases dest: ex_no_sig_Nm ex_no_sig_Var Nm_no_beta Var_no_beta)

lemma ex_NF_Comp_Var_Nm: "NF (Comp (Var 0) (Nm 1))"
  by (rule ex_NF_intro)
    (auto elim!: sig.cases beta.cases dest: ex_no_sig_Var ex_no_sig_Nm Nm_no_beta)

lemma ex_not_fb_App_Id_Var: "\<not> fb (App Id (Var 1))"
  by (simp add: fb_App_iff)

lemma ex_not_fb_App_Nm_Var: "\<not> fb (App (Nm 0) (Var 1))"
  by (simp add: fb_App_iff)

lemma ex_not_fb_Comp_Var_Nm: "\<not> fb (Comp (Var 0) (Nm 1))"
  by (auto elim!: fb.cases inert.cases)

subsection \<open>1. \<open>0\<circ>(\<lambda>1.1)\<close>, a function used as an environment\<close>

lemma ex1_step1: "Comp (Var 0) (Lam 1 (Var 1)) \<rightarrow>\<^sub>v Comp (Var 1) (Extn (Nm 0) 1 Id)"
  by (rule beta_imp_cbv[OF beta.VarLam])

lemma ex1_step2: "Comp (Var 1) (Extn (Nm 0) 1 Id) \<rightarrow>\<^sub>v Nm 0"
  by (rule sig_imp_cbv[OF sig.VarRef])

lemma ex1_red: "Comp (Var 0) (Lam 1 (Var 1)) \<rightarrow>\<^sub>v\<^sup>* Nm 0"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex1_step1)
  apply (rule r_into_rtranclp)
  apply (rule ex1_step2)
  done

lemma ex1_Typ: "Typ (Comp (Var 0) (Lam 1 (Var 1)))"
  by (rule ex_Typ_of_reduct[OF ex1_red NF_Nm FNm])

subsection \<open>2. \<open>(id/0\<cdot>id)\<circ>\<lceil>0\<rceil>\<close>, an environment used as a function\<close>

lemma ex2_step1: "App (Extn Id 0 Id) (Nm 0) \<rightarrow>\<^sub>v Comp (Var 0) (Extn Id 0 Id)"
  by (rule sig_imp_cbv[OF sig.AppConst])

lemma ex2_step2: "Comp (Var 0) (Extn Id 0 Id) \<rightarrow>\<^sub>v Id"
  by (rule sig_imp_cbv[OF sig.VarRef])

lemma ex2_red: "App (Extn Id 0 Id) (Nm 0) \<rightarrow>\<^sub>v\<^sup>* Id"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex2_step1)
  apply (rule r_into_rtranclp)
  apply (rule ex2_step2)
  done

lemma ex2_Typ: "Typ (App (Extn Id 0 Id) (Nm 0))"
  by (rule ex_Typ_of_reduct[OF ex2_red ex_NF_Id FId])

subsection \<open>3. \<open>id 1\<close>, a clash\<close>

lemma ex3_not_Typ: "\<not> Typ (App Id (Var 1))"
  by (rule clash_not_Typ[OF ex_NF_App_Id_Var ex_not_fb_App_Id_Var])

subsection \<open>4. \<open>\<lceil>0\<rceil> 1\<close> and \<open>0\<circ>\<lceil>1\<rceil>\<close>, clashes\<close>

lemma ex4a_not_Typ: "\<not> Typ (App (Nm 0) (Var 1))"
  by (rule clash_not_Typ[OF ex_NF_App_Nm_Var ex_not_fb_App_Nm_Var])

lemma ex4b_not_Typ: "\<not> Typ (Comp (Var 0) (Nm 1))"
  by (rule clash_not_Typ[OF ex_NF_Comp_Var_Nm ex_not_fb_Comp_Var_Nm])

subsection \<open>5. \<open>id((\<lambda>2.\<lceil>0\<rceil>) 1)\<close>, using AppR and Beta2\<close>

lemma ex5_step1:
  "App Id (App (Lam 2 (Nm 0)) (Var 1)) \<rightarrow>\<^sub>v App Id (Comp (Nm 0) (Extn (Var 1) 2 Id))"
  by (rule beta_imp_cbv[OF beta.AppR[OF FId beta.Beta2[OF fb_Var]]])

lemma ex5_step2: "App Id (Comp (Nm 0) (Extn (Var 1) 2 Id)) \<rightarrow>\<^sub>v App Id (Nm 0)"
  by (rule sig_imp_cbv[OF sig.AppR[OF sig.ConstComp]])

lemma ex5_step3: "App Id (Nm 0) \<rightarrow>\<^sub>v Comp (Var 0) Id"
  by (rule sig_imp_cbv[OF sig.AppConst])

lemma ex5_step4: "Comp (Var 0) Id \<rightarrow>\<^sub>v Var 0"
  by (rule sig_imp_cbv[OF sig.IdR])

lemma ex5_red: "App Id (App (Lam 2 (Nm 0)) (Var 1)) \<rightarrow>\<^sub>v\<^sup>* Var 0"
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step1)
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step2)
  apply (rule converse_rtranclp_into_rtranclp)
   apply (rule ex5_step3)
  apply (rule r_into_rtranclp)
  apply (rule ex5_step4)
  done

lemma ex5_Typ: "Typ (App Id (App (Lam 2 (Nm 0)) (Var 1)))"
  by (rule ex_Typ_of_reduct[OF ex5_red NF_Var fb_Var])

end
