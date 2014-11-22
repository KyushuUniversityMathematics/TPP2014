(*==================================================================
This  Isabelle/HOL file contains the proofs of TPPmark2014 problem.
Author:  Fadoua Ghourabi, Kwansei Gakuin University
         (fadouaghourabi@gmail.com)
====================================================================*)
theory TPPmark2014

imports
  Main Semiring_Normalization Orderings

begin


lemmas mult_nat19 =  Semiring_Normalization.comm_semiring_1_class.normalizing_semiring_rules(19)
lemmas mult_nat_comm = comm_semiring_1_class.normalizing_semiring_rules(7)

(*----- Proof of (i) -------- *)
section{*Proof of (i)*}

lemma power2_sum:
fixes a b::"nat"
shows "(a + b)^2 = a^2 + 2*a*b + b^2"
apply (subst power2_eq_square)
apply (subst add_mult_distrib)
apply (subst add_mult_distrib2)+
apply auto
apply (subst power2_eq_square[THEN sym])+
by simp

lemma power2_mod3:
fixes a::nat
shows "\<not> (a^2 mod 3 = 2)"
proof (rule ccontr, simp)
  assume assm:"a^2 mod 3 = 2"

  obtain q::nat where q:"a^2 div 3 = q" by simp
  have apow2:"a^2 = 3*q + 2" 
  apply (subst mod_div_equality2[where ?a = "a^2",THEN sym])
  by (subst assm, subst q, simp)

  obtain q0 r0::nat where r0:"a mod 3 = r0" and q0:"a div 3 = q0" and r0less3:"r0 < 3"  by simp_all
  have a:"a = 3*q0 + r0"
  apply (subst mod_div_equality2[THEN sym])
  by (subst r0, subst q0, simp)

  with apow2 have "(3*q0 + r0)^2 = 3*q + 2" by simp
  then have eq1:"(3*q0)^2 + 2*3*q0*r0 + r0^2 = 3*q + 2" 
  by (subst (asm) power2_sum, simp)

  from r0 have "r0 = 0 \<or> r0 = 1 \<or> r0 = 2" by auto
  then show "False"
  proof 
    assume assm1:"r0 = 0"
    with a have "(3*q0)^2 = a^2" by auto
    then have "3*3*q0^2 = a^2" 
    apply (subst (asm) power2_eq_square, auto)
    apply (subst (asm) power2_eq_square[THEN sym])
    by assumption

    then have b1:"3*3*q0^2 = a^2" by auto
    have "a^2 mod 3 = 0" 
    by (subst b1[THEN sym], subst mod_mult_left_eq, auto)

    with assm show False by simp
  next
    assume "r0 = 1 \<or> r0 = 2" then show False
    proof
      assume assm2:"r0 = 1"
      from a have "(3*q0)^2 + 2*3*q0 + 1 = a^2"
      apply (subst (asm)  assm2)
      apply (erule ssubst)
      by (subst power2_sum, auto)
      
      then have b2:"3*(3*q0^2 + 2*q0) + 1 = a^2" 
      apply (subst (asm) power2_eq_square)
      by (subst (asm) mult_nat19, auto simp:power2_eq_square)
      
      have "a^2 mod 3 = 1"
      apply (subst b2[THEN sym])
      apply (subst Suc_eq_plus1[THEN sym])
      apply (subst  mod_Suc_eq_Suc_mod)
      by (subst mod_mult_self1_is_0, simp)

      with assm show False by simp
    next
      assume assm3:"r0 = 2"
      from a have "(3*q0)^2 + 2*3*q0*2 + 4 = a^2" 
      apply (subst (asm)  assm3)
      apply (erule ssubst)
      by (subst power2_sum, auto)

      then have b2:"3*(3*q0^2 + 2*q0*2 + 1) + 1 = a^2"
      apply (subgoal_tac "4 = 3 +1", auto)
      by (subst (asm) power_mult_distrib, auto)
      
      have "a^2 mod 3 = 1"
      apply (subst b2[THEN sym])
      apply (subst Suc_eq_plus1[THEN sym])
      apply (subst mult_nat_comm[of "3" " Suc (3 * q0\<^sup>2 + 2 * q0 * 2)"])
      by (subst mod_mult_self3, simp)

      with assm show False by simp
   qed
qed
qed

lemma i:
fixes a::nat
shows "(a^2 mod 3 = 0) \<or> (a^2 mod 3 = 1)"
by (insert power2_mod3[of a], auto)

section{*Proof of (ii)*}

lemma three_divides_power2:
fixes a:: nat
assumes "3 dvd (a^2)"
shows "3 dvd a"
proof -
  from assms have apow2:"a*a mod 3 = 0" 
  apply (subst (asm) dvd_eq_mod_eq_0)
  by (subst power2_eq_square[THEN sym], simp)

  obtain q r where q:"a div 3 = q" and r:"a mod 3 = r" by simp_all
  from r have "r = 0 \<or> r = 1 \<or> r = 2"  by auto
  then show ?thesis
  proof 
    assume "r = 0"
    with r have "a mod 3 = 0" by simp
    thus "3 dvd a" by auto
  next
    assume "r = 1 \<or> r = 2"
    then show "3 dvd a"
    proof
      assume "r = 1"
      with q r have a:"a = 3*q + 1" by (metis mod_div_equality2)

      then have a:"a^2 = 3*(3*q^2 + 2*q) + 1"
      by (rule ssubst, subst power2_sum, auto simp:power2_eq_square)
      
      have "a^2 mod 3 = 1" 
      apply (subst a)
      apply (subst Suc_eq_plus1[THEN sym])
      apply (subst  mod_Suc_eq_Suc_mod)
      by (subst mod_mult_self1_is_0, simp)

      with apow2 have False by (subst (asm) power2_eq_square, simp)
      thus "3 dvd a" by simp
   next
      assume "r = 2"
      with q r have a:"a = 3*q + 2" by (metis mod_div_equality2)
      
      then have a:"a^2 = 3*(3*q^2 + 2*q*2+ 1) + 1"
      apply (rule ssubst)
      by (subst power2_sum, auto simp:power2_eq_square)

      have "a^2 mod 3 = 1" 
      apply (subst a)
      apply (subst Suc_eq_plus1[THEN sym])
      apply (subst comm_semiring_1_class.normalizing_semiring_rules(7)[of "3" " Suc (3 * q^2 + 2 * q * 2)"])
      by (subst mod_mult_self3, simp)

      with apow2 have False by (subst (asm) power2_eq_square, simp)
      thus "3 dvd a" by simp
    qed (* case r = 2 \<or> r = 1*)
  qed (* case r = 0 *)
qed

lemma ii:
fixes a b c::nat
assumes "a^2 + b^2 = 3*c^2"
shows "3 dvd a \<and> 3 dvd b \<and> 3 dvd c"
proof (auto)
  from assms have "3 dvd (a^2 + b^2)" by auto
  then have ab:"((a^2 mod 3) + (b^2 mod 3)) mod 3 = 0" 
  by (subst (asm) dvd_eq_mod_eq_0, subst (asm) mod_add_eq, simp)

  have amod3:"a^2 mod 3 = 0 \<or> a^2 mod 3 = 1" by (rule i)
  moreover have bmod3:"b^2 mod 3 = 0 \<or> b^2 mod 3 = 1" by (rule i)
  ultimately have "a^2 mod 3 + b^2 mod 3 = 0 \<or> a^2 mod 3 + b^2 mod 3 = 1 \<or> a^2 mod 3 + b^2 mod 3 = 2"
  by auto
  then have "a^2 mod 3 + b^2 mod 3 = 0" 
  proof 
    assume "a^2 mod 3 + b^2 mod 3 = 0"
    thus ?thesis by simp
  next
    assume "a\<^sup>2 mod 3 + b\<^sup>2 mod 3 = 1 \<or> a\<^sup>2 mod 3 + b\<^sup>2 mod 3 = 2"
    then have "((a^2 mod 3) + (b^2 mod 3)) mod 3 = 1 \<or> ((a^2 mod 3) + (b^2 mod 3)) mod 3 = 2"
    by auto
    with ab have False by simp
    thus ?thesis by simp
  qed

  with amod3 bmod3 have "a^2 mod 3 = 0 \<and> b^2 mod 3 = 0"
  by auto
  then have a2:"3 dvd (a^2)" and b2:"3 dvd (b^2)" by (simp_all add:dvd_eq_mod_eq_0)
  
  from a2 show threedva:"3 dvd a" by (rule three_divides_power2)
  from b2 show threedvb:"3 dvd b" by (rule three_divides_power2)

  from threedva obtain q1 where q1:"a = 3*q1" by (metis dvdE)
  from threedvb obtain q2 where q2:"b = 3*q2" by (metis dvdE)
  with q1 assms have "(3*q1)^2 + (3*q2)^2 = 3*c^2" by auto
  then have "3*(3*q1^2 + 3*q2^2) = 3*c^2" 
  apply (subst (asm) power_mult_distrib)
  apply (subst (asm) power_mult_distrib)
  by auto

  then have "3*q1^2 + 3*q2^2 = c^2" by (simp)
  then have "3 dvd c^2" 
  apply (subst (asm) add_mult_distrib2[THEN sym])
  by (erule subst, simp)

  thus threedvc:"3 dvd c" by (rule three_divides_power2)
qed

(*---------- Proof of (iii) -----------*)
section{*Proof of (iii)*}

lemma div3:
fixes a b c::nat
assumes "a^2 + b^2 = 3*c^2"
shows "(a div 3)^2 + (b div 3)^2 = 3*(c div 3)^2"
proof -

  from assms have a:"3 dvd a" and b:"3 dvd b" and c:"3 dvd c" using ii
  by (simp_all)

  from a b c assms have "(3*(a div 3))^2 + (3*(b div 3))^2 = 3*(3*(c div 3))^2 "
  by (metis dvd_mult_div_cancel)

  then have "9*(a div 3)^2 + 9*(b div 3)^2 = 9*(3*(c div 3)^2)"
  by (auto simp:power_mult_distrib)

  thus ?thesis by auto

qed

lemma iii_c_is_null:
fixes a b c::nat
assumes "a^2+b^2=3*c^2"
shows "c = 0"
proof (rule ccontr)
    assume c:"c \<noteq> 0"
    let ?Sc = "{z::nat. 0 < z \<and> (\<exists>x y::nat. x^2+y^2=3*z^2)}" 
    from assms c have c:"c \<in> ?Sc" by auto
    then obtain cmin::nat where cmin:"cmin = (LEAST x. x \<in> ?Sc)" by auto
    
    { fix z assume "z \<in> ?Sc"
       with cmin have cminlessz:"cmin \<le> z" 
       using Least_le[of "\<lambda>u. 0 < u \<and> (\<exists>x y. x\<^sup>2 + y\<^sup>2 = 3 * u\<^sup>2)" "z"] 
    by auto
    } note res = this
    with c cmin have cmininSc:"cmin \<in> ?Sc" 
    using LeastI[of "\<lambda>u. 0 < u \<and> (\<exists>x y. x\<^sup>2 + y\<^sup>2 = 3 * u\<^sup>2)" "c"] by auto

    then have cminpos:"0 < cmin" by auto
    from cmininSc obtain a0 b0 where sum:"a0^2 + b0^2 = 3*cmin^2" by auto
    then have "3 dvd cmin" using ii by auto
    then have "cmin = 3*(cmin div 3)" 
    apply (subst mult.commute)
    by (erule dvd_div_mult_self[THEN sym])
    with cminpos have cmindiv3:"0 < (cmin div 3)" by simp
    from sum have "(a0 div 3)^2 + (b0 div 3)^2 = 3*(cmin div 3)^2" using div3 by auto
    with cmindiv3 have a1:"(cmin div 3) \<in> ?Sc" by auto
    from cminpos have a2:"cmin div 3 < cmin" using  int_div_less_self by auto
    from res a1 have "cmin \<le> (cmin div 3)" by simp

    with a2 show False by simp
qed    

lemma iii_ab_are_null:
fixes a b c::nat
assumes "a^2 + b^2 = 3*c^2"
shows "a = 0 \<and> b = 0"
proof -
  from assms have "c = 0" using iii_c_is_null by simp
  with assms have "a^2 + b^2 = 0" by simp
  thus "a = 0 \<and> b = 0" by auto
qed


end
