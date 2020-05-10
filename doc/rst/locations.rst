Locations
=========

.. container::
   :name: menu

.. container::
   :name: content

   .. rubric:: Locations
      :name: locations
      :class: top

   The location is a concept often used in Camlp5, bound to where errors
   occur in the source. The basic type is "``Ploc.t``" which is an
   abstract type.

   .. container::
      :name: tableofcontents

   .. rubric:: Definitions
      :name: definitions

   Internally a location is a pair of source *positions*: the beginning
   and the end of an element in the source (file or interactive). A
   located element can be a character (the end is just the beginning
   plus one), a token, or a longer sequence generally corresponding to a
   grammar rule.

   A *position* is a count of characters since the beginning of the
   file, starting at zero. When a couple of positions define a location,
   the first position is the position of the first character of the
   element, and the last position is the first character *not* part of
   the element. The location length is the difference between those two
   numbers. Notice that the position corresponds exactly to the
   character count in the streams of characters.

   In the `extensible grammars <grammars.html>`__, a variable with the
   specific name "``loc``" is predefined in all semantic actions: it is
   the location of the associated rule. Since the `syntax tree
   quotations <ml_ast.html>`__ generate nodes with "``loc``" as location
   part, this allow to generate grammars without having to consider
   source locations.

   It is possible to change the name "``loc``" to another name, through
   the parameter "``-loc``" of the Camlp5 commands.

   Remark: the reason why the type "``location``" is abstract is that in
   future versions, it may contain other informations, such as the
   associated comments, the type (for expressions nodes), things like
   that, without having to change the already written programs.

   .. rubric:: Building locations
      :name: building-locations

   Tools are provided in the module "``Ploc``" to manage locations.

   First, "``Ploc.dummy``" is a dummy location used when the element
   does not correspond to any source, or if the programmer does not want
   to worry about locations.

   The function "``Ploc.make``" builds a location from three parameters:

   -  the line number, starting at 1
   -  the position of the first column of the line
   -  a couple of positions of the location: the first one belonging to
      the given line, the second one being able to belong to another
      line, further.

   If the line number is not known, it is possible to use the function
   "``Ploc.make_unlined``" taking only the couple of positions of the
   location. In this case, error messages may indicate the first line
   and a big count of characters from this line (actually from the
   beginning of the file). With a good text editor, it is possible, to
   find the good location, anyway.

   If the location is built with "``Ploc.make_unlined``", and if your
   program displays a source location itself, it is possible to use the
   function "``Ploc.from_file``" which takes the file name and the
   location as parameters and return, by reading that file, the line
   number, and the character positions of the location.

   .. rubric:: Raising with a location
      :name: raising-with-a-location

   The function "``Ploc.raise``" allows one to raise an exception
   together with a location. All exceptions raised in the `extensible
   grammars <grammars.html>`__ use "``Ploc.raise``". The raised
   exception is "``Ploc.Exc``" with two parameters: the location and the
   exception itself.

   Notice that "``Ploc.raise``" just reraises the exception if it is
   already the exception "``Ploc.Exc``", ignoring then the new given
   location.

   A paradigm to print exceptions possibly enclosed by "``Ploc.Exc``" is
   to write the "``try..with``" statement like this:

   ::

        try ... with exn ->
          let exn =
            match exn with
            [ Ploc.Exc loc exn -> do { ... print the location ...; exn }
            | _ -> exn ]
          in
          match exn with
          ...print the exception which is *not* located...

   .. rubric:: Other functions
      :name: other-functions

   Some other functions are provided:

   ``Ploc.first_pos``
      returns the first position (an integer) of the location.
   ``Ploc.last_pos``
      returns the last position (an integer) of the location (position
      of the first character not belonging to the element.
   ``Ploc.line_nb``
      returns the line number of the location or ``-1`` if the location
      does not contain a line number (i.e. built by
      "``Ploc.make_unlined``").
   ``Ploc.bol_pos``
      returns the position of the beginning of the line of the location.
      It is zero if the location does not contain a line number (i.e.
      built by "``Ploc.make_unlined``").

   And still other ones used in Camlp5 sources:

   ``Ploc.encl``
      "``Ploc.encl loc1 loc2``" returns the location starting at the
      smallest begin of "``loc1``" and "``loc2``" and ending at their
      greatest end.. In simple words, it is the location enclosing
      "``loc1``" and "``loc2``" and all what is between them.
   ``Ploc.shift``
      "``Ploc.shift sh loc``" returns the location "``loc``" shifted
      with "``sh``" characters. The line number is not recomputed.
   ``Ploc.sub``
      "``Ploc.sub loc sh len``" is the location "``loc``" shifted with
      "``sh``" characters and with length "``len``". The previous ending
      position of the location is lost.
   "``Ploc.after``"
      "``Ploc.after loc sh len``" is the location just after "``loc``"
      (i.e. starting at the end position of "``loc``"), shifted with
      "``sh``" characters, and of length "``len``".

   .. container:: trailer
