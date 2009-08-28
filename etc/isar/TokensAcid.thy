(* Some acid tests for token modes in Isabelle
   David Aspinall, 2008-9.
   $Id$
*)

theory TokensAcid imports Main 
begin

(* Symbols.

   Here's a table of all tokens for symbols, produced by
   menu command Tokens -> List Tokens 

   You should see glyphs in all positions except the whitespace
   tokens at the end of row 25 and start of row 26.
*)

(*
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
  20.  \<wrong>	\<acute>	\<index>	\<dieresis>	\<cedilla>	\<hungarumlaut>	\<spacespace>	\<some>	\<stareq>	\<defeq>
  21.  \<questioneq>	\<vartheta>	\<varpi>	\<varrho>	\<varsigma>	\<varphi>	\<hbar>	\<ell>	\<ast>	\<bigcirc>
  22.  \<bigtriangleup>	\<bigtriangledown>	\<ni>	\<mid>	\<notlt>	\<notle>	\<notprec>	\<notpreceq>	\<notsubset>	\<notsubseteq>
  23.  \<notsqsubseteq>	\<notgt>	\<notge>	\<notsucc>	\<notsucceq>	\<notsupset>	\<notsupseteq>	\<notsqsupseteq>	\<notequiv>	\<notsim>
  24.  \<notsimeq>	\<notapprox>	\<notcong>	\<notasymp>	\<nearrow>	\<searrow>	\<swarrow>	\<nwarrow>	\<vdots>	\<ddots>
  25.  \<closequote>	\<openquote>	\<opendblquote>	\<closedblquote>	\<emdash>	\<prime>	\<doubleprime>	\<tripleprime>	\<quadrupleprime>	\<nbspace>
  26.  \<thinspace>	\<notni>	\<colonequals>	\<foursuperior>	\<fivesuperior>	\<sixsuperior>	\<sevensuperior>	\<eightsuperior>	\<ninesuperior>	\<alpha>
  27.  \<beta>	\<gamma>	\<delta>	\<epsilon>	\<zeta>	\<eta>	\<theta>	\<iota>	\<kappa>	\<lambda>
  28.  \<mu>	\<nu>	\<xi>	\<pi>	\<rho>	\<sigma>	\<tau>	\<upsilon>	\<phi>	\<chi>
  29.  \<psi>	\<omega>	\<Gamma>	\<Delta>	\<Theta>	\<Lambda>	\<Xi>	\<Pi>	\<Sigma>	\<Upsilon>
  30.  \<Phi>	\<Psi>	\<Omega>	\<zero>	\<one>	\<two>	\<three>	\<four>	\<five>	\<six>
  31.  \<seven>	\<eight>	\<nine>	\<A>	\<B>	\<C>	\<D>	\<E>	\<F>	\<G>
  32.  \<H>	\<I>	\<J>	\<K>	\<L>	\<M>	\<N>	\<O>	\<P>	\<Q>
  33.  \<R>	\<S>	\<T>	\<U>	\<V>	\<W>	\<X>	\<Y>	\<Z>	 
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

term "a\<^bsub>longsub\<^esub>"
term "b\<^bsup>longsuper\<^esup>"
term "\<^bbold>Bold text \<alpha>\<beta>\<gamma>\<delta> \<in> \<forall>\<^ebold>"
term "\<^bitalic>Italic text \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^eitalic>"  
term "\<^bsans>Sans serif text \<alpha>\<beta>\<gamma>\<delta>\<in>\<forall>\<^esans>"
term "\<^bscript>Script \<alpha>\<beta>\<gamma>\<delta>\<in>\<forall>\<^escript>"
term "\<^bfrakt>Frakt \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^efrakt>"
term "\<^bserif>Roman \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^eserif>"
   

(* Tokens controlling layout and fonts: next character.
 
   These are tokens that affect the following character/identifier only.

   Similar to previous case.

   See Tokens -> Format Char -> ...
*)

(*   NB: below here cannot be processed: just in terms to check with 
     string font for terms. *)

term "a\<^sub>b"   (* NB: here and below cannot be processed *)
term "a\<^sup>b"
term "a\<^isub>b"
term "a\<^isup>b"
term "\<^loc>a"
term "\<^bold>b"
term "\<^italic>b"


(* 
   Variants on token names: different token names,
   same appearance.   Simulated overloading, \<^bitalic>much\<^eitalic> simpler to do
   this in the UI than mess with type classes, etc,
   in the logical framework!

   Demonstration: let's take back \<And> from the meta-level.

   NB: the token scheme mechanism here is a PG convenience,
   in other frontends you may have to define \< AndX> to
   appear in the same way as \< And> individually.
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

(* Note: of course, copy and paste will produce wrong result
   for above: default token <And> without variant is produced! *)



(* More esoteric stuff *)


term "\<^bbig>large text \<alpha> \<beta> \<Sigma>\<^ebig>"

term "\<^bsmall>small\<^esmall>"

term "\<^bunderline>underlined\<^eunderline>"

term "\<^boverline>overlined\<^eoverline>"


(* Bold and italic combinations for regions *)
term "\<^bbold>Bold and \<^bitalic>italic\<^eitalic>\<^ebold>"
term "\<^bitalic>Italic and \<^bbold>bold\<^ebold>\<^eitalic>"

(* Font and weight/shape changes for regions *)
term "\<^bbold>Bold and \<^bscript>script\<^escript>\<^ebold>"
term "\<^bserif>Roman and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^eserif>"
term "\<^bfrakt>Frakt and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^efrakt>"

end
