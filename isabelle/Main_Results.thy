theory Main_Results
  imports Soundness
begin

section \<open>Main results\<close>

text \<open>
  \<^item> \<open>main_characterization\<close>: \<open>Typ M \<longleftrightarrow> CFN M\<close>: \<open>M\<close> is typable iff it reaches a
    clash-free normal form (a fireball).
  \<^item> \<open>main_characterization_SN\<close>: \<open>Typ M \<longleftrightarrow> CFSN M\<close>.
  \<^item> \<open>Typ_imp_SN\<close>: typable terms are strongly normalizing.
\<close>

theorem main_characterization: "Typ M \<longleftrightarrow> CFN M"
  using soundness completeness by blast

theorem main_characterization_SN: "Typ M \<longleftrightarrow> CFSN M"
  using main_characterization CFN_iff_CFSN by blast

theorem Typ_imp_SN: "Typ M \<Longrightarrow> SN_at cbv M"
  using main_characterization_SN by (auto simp: CFSN_def)

corollary clash_not_Typ: "NF M \<Longrightarrow> \<not> fb M \<Longrightarrow> \<not> Typ M"
proof
  assume nf: "NF M" and nfb: "\<not> fb M" and "Typ M"
  then have "CFN M" using main_characterization by blast
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and f: "fb N" unfolding CFN_def by blast
  have "N = M" using normal_rtranclp[OF nf r] .
  then show False using f nfb by simp
qed

text \<open>Oracle check: the main theorems depend on no oracle (in particular no \<open>sorry\<close>).\<close>

ML \<open>
  val ths = [@{thm main_characterization}, @{thm main_characterization_SN}, @{thm Typ_imp_SN},
             @{thm clash_not_Typ}];
  val oracles = Thm_Deps.all_oracles ths;
  val _ = if null oracles then writeln "No oracles."
          else if Config.get @{context} quick_and_dirty
          then warning ("Oracles used (quick_and_dirty): " ^ commas (map (#1 o #1) oracles))
          else error ("Oracles used: " ^ commas (map (#1 o #1) oracles));
\<close>

end
