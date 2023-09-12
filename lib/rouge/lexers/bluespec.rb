module Rouge
  module Lexers
    class BluespecSystemVerilog < RegexLexer
      title "Bluespec SystemVerilog"
      desc "Bluespec SystemVerilog high-Level hardware description language"

      tag 'bluespec'
      aliases 'bsv'

      filenames '*.bsv', '*.ms'  # ms for Minispec
      
      # no BSV mimetype at time of writing

      # All these rules translated from BNF in the BSV language reference guide

      # This is also a rather lazy implementation for most rules. We will correctly lex most
      # correct Bluespec, but we won't catch some technically improper BSV, like calls that 
      # look like system calls (e.g., $finish) but with improper keywords (e.g., $gibberish)

      # INTEGER LITERALS
      IDENTIFIER_TAIL = /[A-Za-z0-9$_]*\b/
      UPPER_IDENTIFIER = /[A-Z]#{IDENTIFIER_TAIL}/  # (Identifier) package names, type names, enumeration labels, union members, and type classes
      LOWER_IDENTIFIER = /[a-z]#{IDENTIFIER_TAIL}/  # (identifier) variables, modules, interfaces
      SYSTEM_IDENTIFIER = /\$#{IDENTIFIER_TAIL}/  # system tasks and functions
      HIDDEN_IDENTIFIER = /_#{IDENTIFIER_TAIL}/  # TODO unused
      
      DEC_DIGITS = /[0-9]+/  # { 0...9 } in BNF
      DEC_DIGITS_UNDERSCORE = /[0-9_]+/
      HEX_DIGITS_UNDERSCORE = /[0-9a-fA-F_]+/
      OCT_DIGITS_UNDERSCORE = /[0-7_]+/
      BIN_DIGITS_UNDERSCORE = /[0-1_]+/
      
      SIGN = /[+-]/
      BIT_WIDTH = /#{DEC_DIGITS}/  # notice no underscores (e.g. Bit#(5))
      DEC_NUM = /#{DEC_DIGITS}#{DEC_DIGITS_UNDERSCORE}?/  # removed redundant DEC_DIGITS; hopefully actually redundant

      BASE_DEC_LITERAL = /('d|'D)#{DEC_DIGITS_UNDERSCORE}/
      BASE_HEX_LITERAL = /('h|'H)#{HEX_DIGITS_UNDERSCORE}/
      BASE_OCT_LITERAL = /('o|'O)#{OCT_DIGITS_UNDERSCORE}/
      BASE_BIN_LITERAL = /('b|'B)#{BIN_DIGITS_UNDERSCORE}/

      # Non-capturing group (?:) is supposed to be better for performance, I hear.
      BASE_LITERAL = /(?:#{BASE_DEC_LITERAL}|#{BASE_HEX_LITERAL}|#{BASE_OCT_LITERAL}|#{BASE_BIN_LITERAL})/

      UNSIZED_INT_LITERAL = /#{SIGN}?(#{BASE_LITERAL}|#{DEC_NUM})/
      SIZED_INT_LITERAL = /#{BIT_WIDTH}#{BASE_LITERAL}/

      INT_LITERAL = /(?:'0|'1|#{SIZED_INT_LITERAL}|#{UNSIZED_INT_LITERAL})/

      # REAL LITERALS
      EXP = /(e|E)/
      REAL_LITERAL = /(?:#{DEC_NUM}(\.#{DEC_DIGITS_UNDERSCORE})?#{EXP}(#{SIGN})?#{DEC_DIGITS_UNDERSCORE}|#{DEC_NUM}\.#{DEC_DIGITS_UNDERSCORE})/

      # STRING LITERALS (unclear if over-capturing per manual)
      STRING_CHARACTER = /[^\n]/  # Manual underspecifies what a "string character" is.
      # ESCAPED_CHAR = /\\[ntvfa"\\]/  # TODO: color escaped characters differently.
      # \OOO and \xHH:  Manual is unclear what it means by "exactly 3 octal digits"

      STRING_LITERAL = /"#{STRING_CHARACTER}*"/

      # DON'T-CARE VALUES
      DONT_CARE = /\?/  # Slightly overcaptures when we have multiple ?'s. TODO fix (low priority)

      # COMPILER DIRECTIVES (TODO not fully supported; just colors full line)
      LAZY_DIRECTIVE = /\`.*\n/
      # DEFINE_DIRECTIVE = /\`define #{LOWER_IDENTIFIER} .*\n/  # Manual uses a curly apostrophe, but compiler uses a backtick.
      # Other keywords too; I'm just doing a blanket backtick check.
      # Also TODO: conditional compilation

      # KEYWORD PROCESSING (TODO: not very performant, but it's what I see other lexers (e.g. Ruby, Go) doing)


      # COMMENTS AND WHITESPACE
      LINE_COMMENT = /\/\/(?:(?!\n).)*/
      COMMENT = /#{LINE_COMMENT}/
      WHITE_SPACE = /\s+/

      # KEYWORDS
      def self.declarations  # I treat these differently because they behave like brackets.
        @declarations ||= Set.new(%w(
          action endaction
          actionvalue endactionvalue
          case endcase
          function endfunction
          instance endinstance
          interface endinterface
          method endmethod
          module endmodule
          package endpackage
          rule endrule
          rules endrules
          typeclass endtypeclass
          enum
          struct
          tagged
          union
          type
          typedef
        ))
      end
      DECLARATION = /\b(?:#{declarations.join('|')})\b/
      # The rule should probably look more like this, but I'm not sure how to do it, and nobody else seems to do it.
      # rule /\w+/ do |m|
      #   if (self.class.declarations.include?(m[0]))
      #     token Keyword::Declaration
      #   end
      # end
      
      def self.reserved
        @reserved ||= Set.new(%w(
          ancestor
          case
          clocked_by
          default
          default_clock
          default_reset
          dependencies
          e
          else
          enable
          export
          for
          if
          ifc_inout
          import
          inout
          input_clock
          input_reset
          let
          match
          matches
          numeric
          output_clock
          output_reset
          parameter
          path
          port
          provisos
          reset_by
          return
          same_family
          schedule
          valueOf
          valueof
          void
          while
        ))
      end
      RESERVED = /\b(?:#{reserved.join('|')})\b/

      def self.default_types  # Notice 
        @default_types ||= Set.new(%W(
          Action
          ActionValue  # todo add '#'
          bit
          let
        ))
      end
      DEFAULT_TYPES = /\b(?:#{default_types.join('|')})\b/

      def self.special_keywords
        @special_keywords ||= Set.new(%w(
          BVI
          C
          CF
          E
          SB
          SBR
        ))
      end  # TODO use

      def self.sv_keywords # SystemVerilog keywords for backwards compatibility
        @sv_keywords ||= Set.new(%w(
          alias
          always
          always_comb
          always_ff
          always_latch
          and
          assert
          assert_strobe
          assign
          assume
          automatic
          before
          begin end
          bind
          bins
          binsof
          bit
          break
          buf
          bufif0
          bufif1
          byte
          case endcase
          casex
          casez
          cell
          chandle
          class endclass
          clocking endclocking
          cmos
          config endconfig
          const
          constraint
          context
          continue
          cover
          covergroup endgroup
          coverpoint
          cross
          deassign
          default
          defparam
          design
          disable
          dist
          do
          edge
          else
          enum
          event
          expect
          export
          extends
          extern
          final
          first_match
          for
          force
          foreach
          forever
          fork
          forkjoin
          function endfunction
          generate endgenerate
          genvar
          highz0
          highz1
          if
          iff
          ifnone
          ignore_bins
          illegal_bins
          import
          incdir
          include
          initial
          inout
          input
          inside
          instance
          int
          integer
          interface endinterface
          intersect
          join
          join_any
          join_none
          large
          liblist
          library
          local
          localparam
          logic
          longint
          macromodule
          matches
          medium
          modport
          module endmodule
          nand
          negedge
          new
          nmos
          nor
          noshowcancelled
          not
          notif0
          notif1
          null
          or
          output
          package endpackage
          packed
          parameter
          pmos
          posedge
          primitive endprimitive
          priority
          program endprogram
          property endproperty
          protected
          pull0
          pull1
          pulldown
          pullup
          pulsestyle_onevent
          pulsestyle_ondetect
          pure
          rand
          randc
          randcase
          randsequence
          rcmos
          real
          realtime
          ref
          reg
          release
          repeat
          return
          rnmos
          rpmos
          rtran
          rtranif0
          rtranif1
          scalared
          sequence endsequence
          shortint
          shortreal
          showcancelled
          signed
          small
          solve
          specify endspecify
          specparam
          static
          string
          strong0
          strong1
          struct
          super
          supply0
          supply1
          table endtable
          tagged
          task endtask
          this
          throughout
          time
          timeprecision
          timeunit
          tran
          tranif0
          tranif1
          tri
          tri0
          tri1
          triand
          trior
          trireg
          type
          typedef
          union
          unique
          unsigned
          use
          var
          vectored
          virtual
          void
          wait
          wait_order
          wand
          weak0
          weak1
          while
          wildcard
          wire
          with
          within
          wor
          xnor
          xor
        ))
      end
      SV_KEYWORDS = /\b(?:#{sv_keywords.join('|')})\b/  # *really* not performant TODO

      PUNCTUATION = /(?:[,;\(\)#]|begin|end)/  # '#' should really go with types TODO

      # "PROPERTIES" or method calls
      METHOD_CALL = /\.#{LOWER_IDENTIFIER}\b/

      # Compiler synthesis directives (TODO make not lazy)
      COMPILER_DIRECTIVE = /\(\*.*\*\)/

      # rule structure based on the go.rb lexer. It seemed very clean.
      state :simple_tokens do
        # Comment-like things
        rule(COMMENT, Comment)
        rule(LAZY_DIRECTIVE, Comment::Preproc)  # `define, but with all `identifier
        rule(COMPILER_DIRECTIVE, Comment::Preproc)  # e.g., (* synthesize *)

        # Keywords
        rule(SYSTEM_IDENTIFIER, Name::Builtin)  # e.g., $display, $format TODO check the word
        rule(DEFAULT_TYPES, Str)
        rule(DECLARATION, Keyword::Declaration)  # TODO: could further split up semantically.
        rule(RESERVED, Keyword::Reserved)  # TODO: could further split up semantically.
        
        # Punctuation
        rule(PUNCTUATION, Punctuation)

        # Legacy keywords from SV
        rule(SV_KEYWORDS, Keyword::Reserved)

        rule(REAL_LITERAL, Num::Other)  # No more specific token available (has to be before)
        rule(INT_LITERAL, Num::Integer)
        # rule(ESCAPED_CHAR, Str::Escape)  # TODO (not implemented; need to play nicely with the string literal rule)
        rule(STRING_LITERAL, Str)
        rule(DONT_CARE, Keyword::Pseudo)
      end

      state :root do
        mixin :simple_tokens
        
        rule(METHOD_CALL, Name::Property)

        # To catch everything else
        rule(LOWER_IDENTIFIER, Name::Variable)  # Lazy
        rule(UPPER_IDENTIFIER, Name::Class)  # Lazy
        rule(WHITE_SPACE, Text::Whitespace)
      end

    end
  end
end
