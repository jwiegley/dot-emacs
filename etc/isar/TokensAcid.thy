(* Some acid tests for token modes *)

theory TokensAcid imports Main 
begin

(*  Here's a table of all tokens for symbols,  
    produced by unicode-tokens-list-tokens *)

(*
\<alpha>	\<beta>	\<gamma>	\<delta>	\<epsilon>	\<zeta>	\<eta>	\<theta>	\<iota>	\<kappa>
\<lambda>	\<mu>	\<nu>	\<xi>	\<pi>	\<rho>	\<sigma>	\<tau>	\<upsilon>	\<phi>
\<chi>	\<psi>	\<omega>	\<Gamma>	\<Delta>	\<Theta>	\<Lambda>	\<Xi>	\<Pi>	\<Sigma>
\<Upsilon>	\<Phi>	\<Psi>	\<Omega>	\<leftarrow>	\<rightarrow>	\<Leftarrow>	\<Rightarrow>	\<leftrightarrow>	\<Leftrightarrow>
\<mapsto>	\<longleftarrow>	\<Longleftarrow>	\<longrightarrow>	\<Longrightarrow>	\<longleftrightarrow>	\<Longleftrightarrow>	\<longmapsto>	\<midarrow>	\<Midarrow>
\<hookleftarrow>	\<hookrightarrow>	\<leftharpoondown>	\<rightharpoondown>	\<leftharpoonup>	\<rightharpoonup>	\<rightleftharpoons>	\<leadsto>	\<downharpoonleft>	\<downharpoonright>
\<upharpoonleft>	\<upharpoonright>	\<restriction>	\<Colon>	\<up>	\<Up>	\<down>	\<Down>	\<updown>	\<Updown>
\<langle>	\<rangle>	\<lceil>	\<rceil>	\<lfloor>	\<rfloor>	\<lparr>	\<rparr>	\<lbrakk>	\<rbrakk>
\<lbrace>	\<rbrace>	\<guillemotleft>	\<guillemotright>	\<bottom>	\<top>	\<and>	\<And>	\<or>	\<Or>
\<forall>	\<exists>	\<nexists>	\<not>	\<box>	\<diamond>	\<turnstile>	\<Turnstile>	\<tturnstile>	\<TTurnstile>
\<stileturn>	\<surd>	\<le>	\<ge>	\<lless>	\<ggreater>	\<in>	\<notin>	\<subset>	\<supset>
\<subseteq>	\<supseteq>	\<sqsubset>	\<sqsupset>	\<sqsubseteq>	\<sqsupseteq>	\<inter>	\<Inter>	\<union>	\<Union>
\<squnion>	\<sqinter>	\<setminus>	\<propto>	\<uplus>	\<noteq>	\<sim>	\<doteq>	\<simeq>	\<approx>
\<asymp>	\<cong>	\<smile>	\<equiv>	\<frown>	\<bowtie>	\<prec>	\<succ>	\<preceq>	\<succeq>
\<parallel>	\<bar>	\<plusminus>	\<minusplus>	\<times>	\<div>	\<cdot>	\<star>	\<bullet>	\<circ>
\<dagger>	\<ddagger>	\<lhd>	\<rhd>	\<unlhd>	\<unrhd>	\<triangleleft>	\<triangleright>	\<triangle>	\<triangleq>
\<oplus>	\<otimes>	\<odot>	\<ominus>	\<oslash>	\<dots>	\<cdots>	\<Sum>	\<Prod>	\<Coprod>
\<infinity>	\<integral>	\<ointegral>	\<clubsuit>	\<diamondsuit>	\<heartsuit>	\<spadesuit>	\<aleph>	\<emptyset>	\<nabla>
\<partial>	\<Re>	\<Im>	\<flat>	\<natural>	\<sharp>	\<angle>	\<copyright>	\<registered>	\<hyphen>
\<inverse>	\<onesuperior>	\<twosuperior>	\<threesuperior>	\<onequarter>	\<onehalf>	\<threequarters>	\<ordmasculine>	\<ordfeminine>	\<section>
\<paragraph>	\<exclamdown>	\<questiondown>	\<euro>	\<pounds>	\<yen>	\<cent>	\<currency>	\<degree>	\<mho>
\<lozenge>	\<wp>	\<wrong>	\<acute>	\<index>	\<dieresis>	\<cedilla>	\<hungarumlaut>	\<spacespace>	\<some>
\<stareq>	\<defeq>	\<questioneq>	\<vartheta>	\<varpi>	\<varrho>	\<varsigma>	\<varphi>	\<hbar>	\<ell>
\<ast>	\<bigcirc>	\<bigtriangleup>	\<bigtriangledown>	\<ni>	\<mid>	\<notlt>	\<notle>	\<notprec>	\<notpreceq>
\<notsubset>	\<notsubseteq>	\<notsqsubseteq>	\<notgt>	\<notge>	\<notsucc>	\<notsucceq>	\<notsupset>	\<notsupseteq>	\<notsqsupseteq>
\<notequiv>	\<notsim>	\<notsimeq>	\<notapprox>	\<notcong>	\<notasymp>	\<nearrow>	\<searrow>	\<swarrow>	\<nwarrow>
\<vdots>	\<ddots>	\<closequote>	\<openquote>	\<opendblquote>	\<closedblquote>	\<emdash>	\<prime>	\<doubleprime>	\<tripleprime>
\<nbspace>	\<thinspace>	\<notni>	\<colonequals>	\<foursuperior>	\<fivesuperior>	\<sixsuperior>	\<sevensuperior>	\<eightsuperior>	\<ninesuperior>
\<zero>	\<one>	\<two>	\<three>	\<four>	\<five>	\<six>	\<seven>	\<eight>	\<nine>
\<A>	\<B>	\<C>	\<D>	\<E>	\<F>	\<G>	\<H>	\<I>	\<J>
\<K>	\<L>	\<M>	\<N>	\<O>	\<P>	\<Q>	\<R>	\<S>	\<T>
\<U>	\<V>	\<W>	\<X>	\<Y>	\<Z>	
*)

(* Demonstrating variants on token names: different token names,
   same appearance.   Simulated overloading.
   Let's take back \<And> from the meta-level.
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

(* Tokens for layout control: next char *)
(* NB: below here cannot be processed: just in terms to check with 
   string font for terms *)
term "a\<^sub>b"
term "a\<^sup>b"
term "a\<^isub>b"
term "a\<^isup>b"
term "\<^loc>a"
term "\<^bold>b"
term "\<^italic>b"

(* Tokens for layout control: regions *)

term "a\<^bsub>long\<^esub>"
term "b\<^bsup>long\<^esup>"
term "\<^bbold>Bold text \<alpha>\<beta>\<gamma>\<delta> \<in> \<forall>\<^ebold>"
term "\<^bitalic>Italic text \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^eitalic>"  
term "\<^bscript>Script \<alpha>\<beta>\<gamma>\<delta>\<in>\<forall>\<^escript>"
term "\<^bfrakt>Frakt \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^efrakt>"
term "\<^bserif>Roman \<alpha>\<beta>\<gamma>\<delta> \<in>\<forall>\<^eserif>"

(* Note: nesting regions not reliable; merging properties flaw? *)
term "\<^bbold>Bold and \<^bitalic>italic\<^eitalic>\<^ebold>"
term "\<^bitalic>Italic and \<^bbold>bold\<^ebold>\<^eitalic>"

(* Font changes work, though *)
term "\<^bbold>Bold and \<^bscript>script\<^escript>\<^ebold>"
term "\<^bserif>Roman and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^eserif>"
term "\<^bfrakt>Frakt and \<^bitalic>italic\<^eitalic> and \<^bbold>bold\<^ebold> \<^efrakt>"

end
