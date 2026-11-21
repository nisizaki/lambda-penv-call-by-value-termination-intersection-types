theory Sigma
  imports Syntax ARS
begin

section \<open>The substitution calculus \<open>\<sigma>\<close>\<close>

text \<open>
  \<open>\<sigma>\<close> is the \<open>\<sigma>\<close>-reduction of \<open>\<lambda>penv\<^sub>w\<^sub>h\<close>: the \<open>\<lambda>env\<close> rules plus
  \<open>AppConst\<close> and \<open>ConstComp\<close>, with all congruences.
\<close>

inductive sig :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<sigma>" 50) where
  Ass: "Comp (Comp L M) N \<rightarrow>\<^sub>\<sigma> Comp L (Comp M N)"
| IdL: "Comp Id M \<rightarrow>\<^sub>\<sigma> M"
| IdR: "Comp M Id \<rightarrow>\<^sub>\<sigma> M"
| DExtn: "Comp (Extn L x M) N \<rightarrow>\<^sub>\<sigma> Extn (Comp L N) x (Comp M N)"
| VarRef: "Comp (Var x) (Extn M x N) \<rightarrow>\<^sub>\<sigma> M"
| VarSkip: "x \<noteq> y \<Longrightarrow> Comp (Var y) (Extn M x N) \<rightarrow>\<^sub>\<sigma> Comp (Var y) N"
| DApp: "Comp (App M1 M2) N \<rightarrow>\<^sub>\<sigma> App (Comp M1 N) (Comp M2 N)"
| AppConst: "App M (Nm x) \<rightarrow>\<^sub>\<sigma> Comp (Var x) M"
| ConstComp: "Comp (Nm x) L \<rightarrow>\<^sub>\<sigma> Nm x"
| AppL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<sigma> App N L"
| AppR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App L M \<rightarrow>\<^sub>\<sigma> App L N"
| Lam: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Lam x M \<rightarrow>\<^sub>\<sigma> Lam x N"
| CompL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>\<sigma> Comp N L"
| CompR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp L M \<rightarrow>\<^sub>\<sigma> Comp L N"
| ExtnL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn M x L \<rightarrow>\<^sub>\<sigma> Extn N x L"
| ExtnR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn L x M \<rightarrow>\<^sub>\<sigma> Extn L x N"

abbreviation sig_normal :: "trm \<Rightarrow> bool" where "sig_normal M \<equiv> normal sig M"

subsection \<open>\<open>\<sigma>\<close> terminates (measure \<^verbatim>\<open>tlength\<close>)\<close>

lemma sig_tlength_decrease: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> tlength N < tlength M"
proof (induction rule: sig.induct)
  case (Ass L M N)
  have eq: "(tlength M + 1) * (tlength N + 1) = tlength M * (tlength N + 1) + tlength N + 1"
    by (simp add: algebra_simps)
  have "tlength M * (tlength N + 1) + 1 < (tlength M + 1) * (tlength N + 1)"
    using eq tlength_pos[of N] by linarith
  then have "tlength L * (tlength M * (tlength N + 1) + 1)
      < tlength L * ((tlength M + 1) * (tlength N + 1))"
    using tlength_pos[of L] by (rule mult_strict_left_mono)
  then show ?case
    by (simp only: tlength.simps mult.assoc)
next
  case (DExtn L x M N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (DApp M1 M2 N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (CompL M N L)
  have "tlength N * (tlength L + 1) < tlength M * (tlength L + 1)"
    using CompL.IH by (rule mult_strict_right_mono) simp
  then show ?case
    by (simp only: tlength.simps)
next
  case (CompR M N L)
  have "tlength L * (tlength N + 1) < tlength L * (tlength M + 1)"
    using CompR.IH tlength_pos[of L] by (intro mult_strict_left_mono) simp_all
  then show ?case
    by (simp only: tlength.simps)
qed simp_all

theorem sig_SN: "SN_at sig M"
proof (induction "tlength M" arbitrary: M rule: less_induct)
  case less
  show ?case
    by (rule SN_atI) (auto intro: less dest: sig_tlength_decrease)
qed

end
