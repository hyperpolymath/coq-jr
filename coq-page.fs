\ SPDX-License-Identifier: AGPL-3.0-or-later
\ SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

\ coq-page.fs - jsCoq page for estate-ssg
\ Uses lib/html.fs for generic HTML generation

include lib/html.fs

\ ============================================================
\ jsCoq-specific helpers
\ ============================================================

: jscoq-name  <span s" jscoq-name" .class )> ." jsCoq" </span> ;

: coq-block  ( id-addr id-u -- )  <textarea .id )> ;
: /coq-block  </textarea> cr ;

\ ============================================================
\ Page content
\ ============================================================

: welcome-section
  <div>
    <h3> ." Welcome to the " jscoq-name ."  Interactive Online System!" </h3>
    <p>
      ." Welcome to the " jscoq-name ."  technology demo! "
      jscoq-name ."  is an interactive, web-based environment for the "
      ." Coq Theorem prover. See the "
      <a s" #team" .href )> ." list of contributors" </a> ."  below."
    </p>
    <p>
      jscoq-name ."  is open source. Feedback welcome at "
      <a s" https://github.com/jscoq/jscoq" .href )> ." GitHub" </a> ." ."
    </p>
  </div> cr ;

: instructions-section
  <div>
    <h4> ." Instructions:" </h4>
    <p> ." Edit and run the Coq code below. Step through proofs with the keyboard." </p>
    <table s" doc-actions" .class )>
      <tr> <th> ." Keys" </th> <th> ." Action" </th> </tr>
      <tr> <td> <kbd> ." Alt+↓/↑" </kbd> </td> <td> ." Step through proof" </td> </tr>
      <tr> <td> <kbd> ." Alt+Enter" </kbd> </td> <td> ." Run to cursor" </td> </tr>
      <tr> <td> <kbd> ." F8" </kbd> </td> <td> ." Toggle goals" </td> </tr>
    </table>
  </div> cr ;

: proof-section
  <div>
    <h4> ." The Infinitude of Primes" </h4>
    <p> ." Georges Gonthier's proof from Mathematical Components:" </p>

    s" addnC" coq-block
    ." From Coq Require Import ssreflect ssrfun ssrbool." cr
    ." From mathcomp Require Import eqtype ssrnat div prime."
    /coq-block

    <h5> ." The Lemma" </h5>
    s" prime_above1" coq-block
    ." Lemma prime_above m : {p | m < p & prime p}." cr
    ." Proof."
    /coq-block

    <p> ." Use pdivP - every number has a prime divisor:" </p>
    s" prime_above2" coq-block
    ." have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1" cr
    ."   by rewrite addn1 ltnS fact_gt0."
    /coq-block

    s" prime_above3" coq-block
    ." exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m."
    /coq-block

    s" prime_above4" coq-block
    ." by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1." cr
    ." Qed."
    /coq-block

    <hr> <p> <em> ." ¡Salut!" </em> </p>
  </div> cr ;

: team-section
  <div s" team" .id )>
    <p> <em> ." Dev team:" </em>
    ."  Emilio J. Gallego Arias (Inria), Shachar Itzhaky (Technion)" </p>
  </div> cr ;

: jscoq-loader
  <script )>
  ." var jscoq_ids=['addnC','prime_above1','prime_above2','prime_above3','prime_above4'];" cr
  ." JsCoq.start(jscoq_ids,{implicit_libs:false,focus:false," cr
  ." editor:{mode:{'company-coq':true},keyMap:'default'}," cr
  ." init_pkgs:['init'],all_pkgs:['coq','mathcomp']});"
  </script> ;

\ ============================================================
\ Main page
\ ============================================================

: coq-page
  <!doctype>
  <html )> cr
  <head>
    <meta .charset s" utf-8" )> cr
    <link .rel s" stylesheet" .href s" styles.css" )> cr
    <script .src s" https://unpkg.com/jscoq@0.18/ui-js/jscoq-loader.js" )> </script>
    <title> ." jsCoq – Coq in Browser" </title>
  </head>
  <body s" jscoq-main" .class )> cr
    s" ide-wrapper toggled" div[
      s" code-wrapper" div[
        s" document" div[
          welcome-section
          instructions-section
          proof-section
          team-section
        ]div
      ]div
    ]div
    jscoq-loader
  </body>
  </html> ;

\ Build commands
: build   ['] coq-page s" output/index.html" >file ." → output/index.html" cr ;
: preview coq-page ;
