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


end
