(* 
   Some acid tests for token modes in Isabelle
   David Aspinall, 2008-9.
   $Id$

   Note:
    Unicode Tokens mode works much better in Emacs 23 than 22.

   jEdit properties :tabSize=8:indentSize=8:noTabs=false:
*)

theory TokensAcid imports Main 
begin

(* Symbols.

   Here's a table of all the standardly defined tokens for symbols,
   produced by menu command Tokens -> List Tokens

   You should see glyphs in all positions except the whitespace
   tokens at positions 208, 262 and 263.
 
   I recommend using StixGeneral for symbols.
   See http://www.stixfonts.org/
   To install on Ubuntu, try:  

         sudo apt-get install fonts-stix

   Other good choices are: Lucida Grande, Lucida Sans Unicode, 
   or DejaVuLGC Sans Mono.

   Unfortunately 


 1.  \<leftarrow>	\<rightarrow>	\<Leftarrow>	\<Rightarrow>	\<leftrightarrow>	\<Leftrightarrow>	\<mapsto>	\<longleftarrow>	\<Longleftarrow>	\<longrightarrow>
 2.  \<Longrightarrow>	\<longleftrightarrow>	\<Longleftrightarrow>	\<longmapsto>	\<midarrow>	\<Midarrow>	\<hookleftarrow>	\<hookrightarrow>	\<leftharpoondown>	\<rightharpoondown>
 3.  \<leftharpoonup>	\<rightharpoonup>	\<rightleftharpoons>	\<leadsto>	\<downharpoonleft>	\<downharpoonright>	\<upharpoonleft>	\<upharpoonright>	\<restriction>	\<Colon>
 4.  \<up>	\<Up>	\<down>	\<Down>	\<updown>	\<Updown>	\<langle>	\<rangle>	\<lceil>	\<rceil>
 5.  \<lfloor>	\<rfloor>	\<lparr>	\<rparr>	\<lbrakk>	\<rbrakk>	\<lbrace>	\<rbrace>	\<guillemotleft>	\<guillemotright>
 6.  \<bottom>	\<top>	\<and>	\<And>	\<or>	\<Or>	\<forall>	\<exists>	\<nexists>	\<not>
 7.  \<box>	\<diamond>	\<turnstile>	\<Turnstile>	\<tturnstile>	\<TTurnstile>	\<stileturn>	\<surd>	\<le>	\<ge>
 8.  \<lless>	\<ggreater>	\<lesssim>	\<greatersim>	\<lessapprox>	\<greaterapprox>	\<in>	\<notin>	\<subset>	\<supset>
 9.  \<subseteq>	\<supseteq>	\<sqsubset>	\<sqsupset>	\<sqsubseteq>	\<sqsupseteq>	\<inter>	\<Inter>	\<union>	\<Union>
10.  \<squnion>	\<Squnion>	\<sqinter>	\<Sqinter>	\<setminus>	\<propto>	\<uplus>	\<Uplus>	\<noteq>	\<sim>
11.  \<doteq>	\<simeq>	\<approx>	\<asymp>	\<cong>	\<smile>	\<equiv>	\<frown>	\<Join>	\<bowtie>
12.  \<prec>	\<succ>	\<preceq>	\<succeq>	\<parallel>	\<bar>	\<plusminus>	\<minusplus>	\<times>	\<div>
13.  \<cdot>	\<star>	\<bullet>	\<circ>	\<dagger>	\<ddagger>	\<lhd>	\<rhd>	\<unlhd>	\<unrhd>
14.  \<triangleleft>	\<triangleright>	\<triangle>	\<triangleq>	\<oplus>	\<Oplus>	\<otimes>	\<Otimes>	\<odot>	\<Odot>
15.  \<ominus>	\<oslash>	\<dots>	\<cdots>	\<Sum>	\<Prod>	\<Coprod>	\<infinity>	\<integral>	\<ointegral>
16.  \<clubsuit>	\<diamondsuit>	\<heartsuit>	\<spadesuit>	\<aleph>	\<emptyset>	\<nabla>	\<partial>	\<Re>	\<Im>
17.  \<flat>	\<natural>	\<sharp>	\<angle>	\<copyright>	\<registered>	\<hyphen>	\<inverse>	\<onesuperior>	\<twosuperior>
18.  \<threesuperior>	\<onequarter>	\<onehalf>	\<threequarters>	\<ordmasculine>	\<ordfeminine>	\<section>	\<paragraph>	\<exclamdown>	\<questiondown>
19.  \<euro>	\<pounds>	\<yen>	\<cent>	\<currency>	\<degree>	\<amalg>	\<mho>	\<lozenge>	\<wp>
20.  \<wrong>	\<struct>	\<acute>	\<index>	\<dieresis>	\<cedilla>	\<hungarumlaut>	\<spacespace>	\<module>	\<some>
21.  \<stareq>	\<defeq>	\<questioneq>	\<vartheta>	\<varpi>	\<varrho>	\<varsigma>	\<varphi>	\<hbar>	\<ell>
22.  \<ast>	\<bigcirc>	\<bigtriangleup>	\<bigtriangledown>	\<ni>	\<mid>	\<notlt>	\<notle>	\<notprec>	\<notpreceq>
23.  \<notsubset>	\<notsubseteq>	\<notsqsubseteq>	\<notgt>	\<notge>	\<notsucc>	\<notsucceq>	\<notsupset>	\<notsupseteq>	\<notsqsupseteq>
24.  \<notequiv>	\<notsim>	\<notsimeq>	\<notapprox>	\<notcong>	\<notasymp>	\<nearrow>	\<searrow>	\<swarrow>	\<nwarrow>
25.  \<vdots>	\<ddots>	\<closequote>	\<openquote>	\<opendblquote>	\<closedblquote>	\<emdash>	\<prime>	\<doubleprime>	\<tripleprime>
26.  \<quadrupleprime>	\<nbspace>	\<thinspace>	\<notni>	\<colonequals>	\<foursuperior>	\<fivesuperior>	\<sixsuperior>	\<sevensuperior>	\<eightsuperior>
27.  \<ninesuperior>	\<bool>	\<complex>	\<nat>	\<rat>	\<real>	\<int>	\<alpha>	\<beta>	\<gamma>
28.  \<delta>	\<epsilon>	\<zeta>	\<eta>	\<theta>	\<iota>	\<kappa>	\<lambda>	\<mu>	\<nu>
29.  \<xi>	\<pi>	\<rho>	\<sigma>	\<tau>	\<upsilon>	\<phi>	\<chi>	\<psi>	\<omega>
30.  \<Gamma>	\<Delta>	\<Theta>	\<Lambda>	\<Xi>	\<Pi>	\<Sigma>	\<Upsilon>	\<Phi>	\<Psi>
31.  \<Omega>	\<zero>	\<one>	\<two>	\<three>	\<four>	\<five>	\<six>	\<seven>	\<eight>
32.  \<nine>	\<A>	\<B>	\<C>	\<D>	\<E>	\<F>	\<G>	\<H>	\<I>
33.  \<J>	\<K>	\<L>	\<M>	\<N>	\<O>	\<P>	\<Q>	\<R>	\<S>
34.  \<T>	\<U>	\<V>	\<W>	\<X>	\<Y>	\<Z>	\<a>	\<b>	\<c>
35.  \<d>	\<e>	\<f>	\<g>	\<h>	\<i>	\<j>	\<k>	\<l>	\<m>
36.  \<n>	\<o>	\<p>	\<q>	\<r>	\<s>	\<t>	\<u>	\<v>	\<w>
37.  \<x>	\<y>	\<z>	\<AA>	\<BB>	\<CC>	\<DD>	\<EE>	\<FF>	\<GG>
38.  \<HH>	\<II>	\<JJ>	\<KK>	\<LL>	\<MM>	\<NN>	\<OO>	\<PP>	\<QQ>
39.  \<RR>	\<SS>	\<TT>	\<UU>	\<VV>	\<WW>	\<XX>	\<YY>	\<ZZ>	\<aa>
40.  \<bb>	\<cc>	\<dd>	\<ee>	\<ff>	\<gg>	\<hh>	\<ii>	\<jj>	\<kk>
41.  \<ll>	\<mm>	\<nn>	\<oo>	\<pp>	\<qq>	\<rr>	\<ss>	\<tt>	\<uu>
42.  \<vv>	\<ww>	\<xx>	\<yy>	\<zz>	 	 	 	 	 
*)

(* Tokens controlling layout and fonts: regions.

   Token region convention in Isabelle is \<^bFOO>... \<^eFOO>
  
   The \<^bserif>font\<^eserif> and \<^bbold>bold\<^ebold>/\<^bitalic>italic\<^eitalic> controls are non-standard and
   may not be supported by other interfaces.

   Convenience functions:
     Select a region, use Tokens -> Format Region -> Bold, etc
  
   Editing can be a bit fiddly, use C-c C-t C-t to show or hide
   the control tokens to help.
*)  

(* Introduce uninterpreted term syntax using these features,
   to check behaviour in locked/unlocked regions. *)

consts longsub :: "['a,'a]\<Rightarrow>'a" ("_\<^bsub>_\<^esub>")
consts longsup :: "['a,'a]\<Rightarrow>'a" ("_\<^bsup>_\<^esup>")

consts bold    :: "'a\<Rightarrow>'a" ("\<^bbold>_\<^ebold>")
consts italic  :: "'a\<Rightarrow>'a" ("\<^bitalic>_\<^eitalic>")
consts sans    :: "'a\<Rightarrow>'a" ("\<^bsans>_\<^esans>")
consts script  :: "'a\<Rightarrow>'a" ("\<^bscript>_\<^escript>")
consts frakt   :: "'a\<Rightarrow>'a" ("\<^bfrakt>_\<^efrakt>")
consts serif   :: "'a\<Rightarrow>'a" ("\<^bserif>_\<^eserif>")

term "a\<^bsub>longsub\<^esub>"   term "b\<^bsup>longsuper\<^esup>"

term "\<^bbold>Bold text\<^ebold>"  term "\<^bitalic>Italic text \<alpha> \<beta>\<^eitalic>"  
term "\<^bsans>Sans \<gamma>\<^esans>"     term "\<^bscript>Script text\<^escript>"
term "\<^bfrakt>Frakt stuff\<^efrakt>"  term "\<^bserif>Roman stuff\<^eserif>"
   
lemma "\<lbrakk> \<^bbold>(Bold text)\<^ebold>; Q \<rbrakk> \<Longrightarrow> Q"
by auto

(* Tokens controlling layout and fonts: next character.
   These are tokens that affect the following character/identifier only.
   Similar to previous case.

   See Tokens -> Format Char -> ...
*)

consts shortsub :: "['a,'a]\<Rightarrow>'a" ("_\<^sub>_")
consts shortsup :: "['a,'a]\<Rightarrow>'a" ("_\<^sup>_")

consts charloc    :: "['a,'a]\<Rightarrow>'a" ("\<^loc>_")
consts charbold   :: "['a,'a]\<Rightarrow>'a" ("\<^bold>_")
consts charitalic :: "['a,'a]\<Rightarrow>'a" ("\<^italic>_")

term "a\<^sub>b"
term "a\<^sup>b"
term "\<^loc>a"
term "\<^bold>b"
term "\<^italic>b"

(* Further examples *)

term "a\<^isub>\<gamma>\<delta>"     (* subscripted gamma  *)
term "a\<^isub>def"  (* no subscript on ef *)

term "a\<^isub>x\<^isub>y"      (* x and y subscripted individually *)
term "a\<^isub>xabc\<^isub>y"   (* x and y should be subscripted, but not ab *)

(* 
   Variants on token names: different token names,
   same appearance.   Simulated overloading, \<^bitalic>much\<^eitalic> simpler to do
   this in the UI than mess with type classes, etc,
   in the logical framework!

   Demonstration: let's take back \<And> from the meta-level.

   NB: the token scheme mechanism here is a PG convenience,
   in other frontends you may have to define \ < AndX> to
   appear in the same way as \ < And> individually.
   Similarly for LaTeX output.

   Use C-c C-t C-z to toggle the display of tokens.
*)

consts 
   andprops :: "bool set \<Rightarrow> bool"	   
   andpreds :: "('a \<Rightarrow> bool) set \<Rightarrow> bool"   

notation (xsymbols)
   andprops ("\<And1>") and   (* token <And1>, hover to see this *)
   andpreds ("\<And2>")       (* token <And2>, hover to see this *)

term "\<And1> {True, False}"		  
term "\<And2> {\<lambda> x. True, \<lambda> y. False}"

(* Note: of course, copy and paste using Unicode to another
   application (Tokens \<rightarrow> Copy As Unicode) and then re-reading in
   Isabelle using another interface will probably produce the wrong
   result.  But copy-pasting within Proof General Emacs is fine since
   the underlying token text is copied, not the presentation.
   What happens is that the text properties are "sticky" and
   copied as well, so you see them even in non-Unicode Tokens buffers.
   But if you save and revisit, you'll see the real text.
*)


(* More esoteric non-standard stuff: unlikely in other interfaces *)

consts 
  shout :: "'a \<Rightarrow> 'a"
  whisper :: "'a \<Rightarrow> 'a"
  underline :: "'a \<Rightarrow> 'a"
  overline :: "'a \<Rightarrow> 'a"

notation (xsymbols)
  shout ("\<^bbig>_\<^ebig>") and
  whisper ("\<^bsmall>_\<^esmall>") and
  underline ("\<^bunderline>_\<^eunderline>") and
  overline ("\<^boverline>_\<^eoverline>")

term "\<^bbig>large text \<alpha> \<beta> \<Sigma> \<integral>\<^ebig>"

term "\<^bsmall>smaller text ((\<alpha> \<and> \<beta>) \<longrightarrow> \<gamma>) \<^esmall>"

term "\<^bunderline>underlined\<^eunderline>"

term "\<^boverline>overlined\<^eoverline>"


(* Bold and italic combinations for regions *)
term "\<^bbold>Bold and (\<^bitalic>italic\<^eitalic>)\<^ebold>"
term "\<^bitalic>Italic and \<^bbold>bold\<^ebold>\<^eitalic>"

(* Font and weight/shape changes for regions *)
term "\<^bbold>Bold and \<^bscript>script\<^escript>\<^ebold>"
term "\<^bserif>Roman and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^eserif>"
term "\<^bfrakt>Frakt and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^efrakt>"

(* Spanning identifier supers/subs: not included in standard Isabelle lexer/latex *)

(* term "a\<^bisup>bcd\<^eisup>"
   term "a\<^bisub>bcd\<^eisub>"  *)

end
