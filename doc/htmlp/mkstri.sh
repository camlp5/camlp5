#!/bin/sh
# mkstri.sh,v

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
  <!-- mkstri.sh,v -->
  <!-- Copyright (c) INRIA 2007-2017 -->
  <title>AST - strict</title>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
  <meta http-equiv="Content-Style-Type" content="text/css" />
  <link rel="stylesheet" type="text/css" href="styles/base.css"
        title="Normal" />
  <style type="text/css">
    .nodelist { margin-left: 2cm }
    table { margin-left: 1cm }
    td { padding-right: 2mm }
  </style>
</head>
<body>

<div id="menu">
</div>

<div id="content">

<h1 class="top">Syntax tree - strict mode</h1>

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

  class=' class="nodelist"'
  if [ "$q" = "type_decl" ]; then
    class="";
    echo '<dl>'
    echo '  <dd>'
  fi

  $top/meta/camlp5r -nolib $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -l200 -impl $top/test/quot_r.ml |
  paste -d@ $file - |
  sed -e 's/(\*.*\*)@//; /\*)$/N; s/\n//' |
  grep "<:$q<" |
  sed -e "s|(\* |  </dd>@</dl>@<dl$class>@  <dt>- |" |
  sed -e 's| \*)|</dt>@  <dd>@    <tt style="color:blue">|' |
  sed -e 's|&|\&amp;|g; s|<:\([a-z_]*\)<|\&lt;:\1\&lt;|' |
  sed -e 's|{<|{\&lt;|; s| < | \&lt; |' |
  sed -e 's| >>;@| >></tt><br/>@    <tt style="color:red">|' |
  sed -e 's|;$|</tt>|' |
  sed -e 's|^&|    <br/><br/>@    <tt style="color:blue">\&|' |
  sed -e '1s|^  </dd>[^@]*@[^@]*@||' |
  sed -e '1s|^    <br/><br/>@||' |
  tr '@' '\n'
  echo '  </dd>'
  echo '</dl>'

done

echo
echo '<div class="trailer">
</div>

</div>

</body>
</html>'
