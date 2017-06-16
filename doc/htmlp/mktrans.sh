#!/bin/sh
# mktrans.sh,v

top=../..
file=$top/test/quot_r.ml
quotation_list="$*"
if [ "$quotation_list" = "" ]; then
  quotation_list="expr patt ctyp str_item sig_item module_expr module_type class_expr class_type class_str_item class_sig_item type_decl with_constr poly_variant"
fi

echo '<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
 "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <!-- mktrans.sh,v -->
  <!-- Copyright (c) INRIA 2007-2017 -->
  <title>AST - transitional</title>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
  <meta http-equiv="Content-Style-Type" content="text/css" />
  <link rel="stylesheet" type="text/css" href="styles/base.css"
        title="Normal" />
  <style type="text/css"><!--
    table { margin-left: 1cm }
    td { padding-right: 2mm }
  --></style>
</head>
<body>

<div id="menu">
</div>

<div id="content">

<h1 class="top">Syntax tree - transitional mode</h1>

<p>This chapter presents the Camlp5 syntax tree when Camlp5 is installed
  in <em>transitional</em> mode.</p>

<div id="tableofcontents">
</div>

<h2>Nodes and Quotations</h2>'

for q in $quotation_list; do

  if [ "$q" = "expr" -o "$q" = "patt" -o "$q" = "ctyp" ]; then
    n=3
  else
    do3=""
    if [ "$q" = "str_item" -o "$q" = "sig_item" -o "$q" = "module_expr" -o \
         "$q" = "module_type" ]
    then
      if [ "$tit3" != "modules..." ]; then do3="modules..."; fi
    elif [ "$q" = "class_expr" -o "$q" = "class_type" -o \
           "$q" = "class_str_item" -o "$q" = "class_sig_item" ]
    then
      if [ "$tit3" != "classes..." ]; then do3="classes..."; fi
    else
      if [ "$tit3" != "other" ]; then do3="other"; fi
    fi
    if [ "$do3" != "" ]; then
      tit3="$do3"
      echo
      echo "<h3>$tit3</h3>"
      fi
    n=4
  fi

  echo
  echo "<h$n>$q</h$n>"
  echo

  h="$(grep $q: $file | sed -e 's/^.*: //; s/...$//')"
  if [ "$h" != "" ]; then
    echo "<p>$h</p>"
    echo
  fi

  echo '<table border="1">'
  echo '  <tr>'
  echo '    <th>Node</th>'
  echo "    <th><tt>&lt;:$q&lt; ... >></tt></th>"
  if [ "$q" != "type_decl" ]; then echo '    <th>Comment</th>'; fi
  echo '  </tr>'
  echo '  <tr>'

  $top/meta/camlp5r -nolib $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -mode T -l200 -impl $file |
  paste -d@ $file - |
  sed -e 's/(\*.*\*)@//; /\*)$/N; s/\n//' |
  sed -e '/(\*/{h; s/\*).*$/\*)/; x}; /^</{G; s/^\(.*\)\n\(.*\)$/\2\1/}' |
  sed -e '/@{/s/(\*.*\*)/(*  *)/' |
  grep "<:$q<" |
  grep -v '$_' |
  sed -e 's/\((\*.*\*)\)\(.*\)$/\2@\1/' |
  sed -e 's/^\([^@]*\)@\([^@]*\)@/\2@\1@/' |
  sed -e 's/&/\&amp;/g; s/ < / \&lt; /g; s/ {< / {\&lt; /g; s/>>;/>>/' |
  sed -e 's/<:[^<]*< /    <td align="center"><tt>/; s|;@|</tt></td>@|' |
  sed -e 's/^MLast./    <td><tt>/; s| >>|</tt></td>|' |
  sed -e 's/^{MLast./    <td><tt>{/' |
  sed -e 's|$|@  </tr>@  <tr>|; s/(\* /    <td>/;s| \*)|</td>|; $s|@  <tr>||' |
  tr '@' '\n' |
  sed -e '/; MLast./{s/; MLast./;/g; s/ = /=/g}' |
  grep -v '<td></td>'

  echo '</table>'
done

echo
echo '<div class="trailer">
</div>

</div>

</body>
</html>'
