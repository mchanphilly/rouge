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

      # IDENTIFIERS
      IDENTIFIER_TAIL = /[A-Za-z0-9$_]*/
      UPPER_IDENTIFIER = /[A-Z]#{IDENTIFIER_TAIL}#?/  # (Identifier) package names, type names, enumeration labels, union members, and type classes
      LOWER_IDENTIFIER = /[a-z]#{IDENTIFIER_TAIL}/  # (identifier) variables, modules, interfaces
      SYSTEM_IDENTIFIER = /\$#{IDENTIFIER_TAIL}/  # system tasks and functions
      HIDDEN_IDENTIFIER = /_#{IDENTIFIER_TAIL}/  # TODO unused
      
      # INTEGER LITERALS
      DEC_DIGITS = /[0-9]+/  # { 0...9 } in BNF
      DEC_DIGITS_UNDERSCORE = /[0-9_]+/
      HEX_DIGITS_UNDERSCORE = /[0-9a-fA-F_]+/
      OCT_DIGITS_UNDERSCORE = /[0-7_]+/
      BIN_DIGITS_UNDERSCORE = /[0-1_]+/
      
      SIGN = /[+-]/
      BIT_WIDTH = /#{DEC_DIGITS}/  # notice no underscores (e.g. Bit#(5))
      DEC_NUM = /#{DEC_DIGITS}#{DEC_DIGITS_UNDERSCORE}?/

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
      ESCAPED_CHAR = /\\[ntvfa"\\]/  # TODO: color escaped characters differently.
      FORMAT_SPECIFIER = /%#{DEC_DIGITS}?[dbohcstmx]/
      # \OOO and \xHH:  Manual is unclear what it means by "exactly 3 octal digits"

      # STRING_LITERAL = /"#{STRING_CHARACTER}*"/

      # DON'T-CARE VALUES
      DONT_CARE = /\?/  # Slightly overcaptures when we have multiple ?'s. TODO fix (low priority)

      # COMPILER DIRECTIVES (TODO not fully supported; just colors full line)
      LAZY_DIRECTIVE = /\`.*\n/
      # DEFINE_DIRECTIVE = /\`define #{LOWER_IDENTIFIER} .*\n/  # Manual uses a curly apostrophe, but compiler uses a backtick.
      # Other keywords too; I'm just doing a blanket backtick check.
      # Also TODO: conditional compilation

      # KEYWORD PROCESSING (TODO: not very performant, but it's what I see other lexers (e.g. Ruby, Go) doing)

      # COMMENTS AND WHITESPACE
      # TODO: highlight TODO, NOTE, or other keywords of note inside of comments.
      LINE_COMMENT = /\/\/(?:(?!\n).)*/
      COMMENT = /#{LINE_COMMENT}/
      WHITE_SPACE = /\s+/

      def self.generic_declarations
        @generic_declarations ||= Set.new(%w(
          function instance interface method module package rule rules typeclass
          typedef struct tagged union enum endfunction endinstance endinterface
          endmethod endmodule endpackage endrule endrules endtypeclass
        ))
      end

      GENERIC_DECLARATIONS = /\b(?:#{generic_declarations.join('|')})\b/
      
      # TODO make this actually more regular instead of ad hoc
      # declared interface, module, function, method, rule names
      # I split the declarations into two types:
      #   1-degree named declarations (module/rule identifier)
      #   2-degree named declarations (second) (function/method RETURN_VALUE identifier)
      # both mixin the :root to cover up the rest of the rules
      # After writing out each of the rules, I realized you can combine the rules because
      # we can just pop after the first identifier.
      SPECIAL_DECLARATIONS = /(module|rule|function|method)/
      # Pretty plausible that there are more declarations to add; but these cover a very solid portion of my usage.

      # KEYWORDS
      def self.control  # Mostly control; I slipped a type in there.
        @control ||= Set.new(%w(
          case endcase type else for if return while
        ))
      end
      CONTROL = /\b(?:#{control.join('|')})\b/
      # The rule should probably look more like this, but I'm not sure how to do it, and nobody else seems to do it.
      # rule /\w+/ do |m|
      #   if (self.class.control.include?(m[0]))
      #     token Keyword::Declaration
      #   end
      # end
      
      def self.reserved
        @reserved ||= Set.new(%w(
          action endaction actionvalue endactionvalue ancestor clocked_by default
          default_clock default_reset dependencies e enable export ifc_inout import
          inout input_clock input_reset let match matches numeric output_clock
          output_reset parameter path port provisos deriving reset_by same_family
          schedule valueOf valueof void
        ))
      end
      RESERVED = /\b(?:#{reserved.join('|')})\b/

      def self.default_types  # Notice 
        @default_types ||= Set.new([
          "ActionValue#",  # The ordering is significant. We don't want to just capture the Action.
          "Action",
          "bit",
          "let"
        ])
      end
      DEFAULT_TYPES = /(?:#{default_types.join('|')})/

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

      def self.sv_keywords # SystemVerilog keywords for backwards compatibility. Overlaps with other sets.
        @sv_keywords ||= Set.new(%w(
          alias always always_comb always_ff always_latch and assert assert_strobe
          assign assume automatic before begin end bind bins binsof bit break buf
          bufif0 bufif1 byte case endcase casex casez cell chandle class endclass
          clocking endclocking cmos config endconfig const constraint context continue
          cover covergroup endgroup coverpoint cross deassign default defparam design
          disable dist do edge else enum event expect export extends extern final 
          first_match for force foreach forever fork forkjoin function endfunction
          generate endgenerate genvar highz0 highz1 if iff ifnone ignore_bins
          illegal_bins import incdir include initial inout input inside instance
          int integer interface endinterface intersect join join_any join_none
          large liblist library local localparam logic longint macromodule
          matches medium modport module endmodule nand negedge new nmos nor
          noshowcancelled not notif0 notif1 null or output package endpackage
          packed parameter pmos posedge primitive endprimitive priority program
          endprogram property endproperty protected pull0 pull1 pulldown pullup
          pulsestyle_onevent pulsestyle_ondetect pure rand randc randcase randsequence
          rcmos real realtime ref reg release repeat return rnmos rpmos rtran
          rtranif0 rtranif1 scalared sequence endsequence shortint shortreal
          showcancelled signed small solve specify endspecify specparam static
          string strong0 strong1 struct super supply0 supply1 table endtable
          tagged task endtask this throughout time timeprecision timeunit tran
          tranif0 tranif1 tri tri0 tri1 triand trior trireg type typedef
          union unique unsigned use var vectored virtual void wait wait_order
          wand weak0 weak1 while wildcard wire with within wor xnor xor
      ))
      end
      SV_KEYWORDS = /\b(?:#{sv_keywords.join('|')})\b/  # *really* not performant TODO

      PUNCTUATION = /(?:[.,;#]|begin|end)/  # '#' should really go with types TODO

      # Things that follow .  (method calls and match unpacking)
      # e.g., match Status {someIndex: .someIndex} = counter.get_status;
      #                                ^^^^^^^^^^
      MATCH_UNPACK= /\s\.#{LOWER_IDENTIFIER}/
      # TODO check if whitespace actually breaks method calls; if not, then we need to find a different rule. 
      METHOD_CALL = /\.#{LOWER_IDENTIFIER}/
      
      # An action function can stand alone.
      # We need to match the following:
      #   - do_thing;
      #   - do_thing(blah, blah, blah);
      # This regex checks that we have a newline, whitespace, and an identifier. We lookahead to check for ( or ;
      STANDALONE_CALL = /(?m)^\n\s*#{LOWER_IDENTIFIER}(?=[\(;])/

      # Compiler synthesis directives (TODO make not lazy)
      COMPILER_DIRECTIVE = /\(\*.*\*\)/

      # Operators
      ACTIONVALUE_ARROW = /<-/
      OPERATORS = /[\:=\+\-\!~&|\/%<>\(\)\{\}\[\]]+/  # TODO change to actual operators and not lazy


      # ENUM
      # Because enums and interfaces both use UPPER_IDENTIFIER, it can be difficult to distinguish
      # them in lexing. We need to be more discerning in the rules we use.
      
      # Looking at a snippet of Bluespec, we can see that generally (I don't know about strict
      # adherance to the grammar):

      # Enumeration (members) are (and interfaces aren't):
      # - in comma separated curly bracket lists {One, Two, Three} when defined
      # - used with operators; e.g. comparison operator
      # - in case statements

      CASE_ENUM = /#{UPPER_IDENTIFIER}(?=:)/

      # rule structure based on the go.rb lexer. It seemed very clean.

      state :simple_tokens do
        # Comment-like things
        rule(COMMENT, Comment)
        rule(LAZY_DIRECTIVE, Comment::Preproc)  # `define, but with all `identifier
        rule(COMPILER_DIRECTIVE, Name::Function::Magic)  # e.g., (* synthesize *)

        # Keywords
        rule(SYSTEM_IDENTIFIER, Name::Builtin)  # e.g., $display, $format TODO check the word
        
        # Literals
        rule(REAL_LITERAL, Num)  # No more specific token available (has to be before)
        rule(INT_LITERAL, Num::Integer)
        # rule(ESCAPED_CHAR, Str::Escape)  # TODO (not implemented; need to play nicely with the string literal rule)
        rule(/"/, Str::Delimiter, :string)

        # Punctuation
        rule(ACTIONVALUE_ARROW, Operator, :actionvalue)
        rule(OPERATORS, Operator)

        rule(DONT_CARE, Keyword::Pseudo)
      end

      state :root do
        rule(DEFAULT_TYPES, Keyword)

        mixin :simple_tokens  # Mostly keywords

        # Declarations
        rule(%r/typedef\s+enum/, Keyword::Declaration, :enum_declaration) # typedef enum
        rule(%r/case/, Keyword::Reserved, :case)

        rule(SPECIAL_DECLARATIONS, Keyword::Declaration, :declared) # module, rule, interface, function, etc.
        rule(GENERIC_DECLARATIONS, Keyword::Declaration) # endmodule, everything that's left, etc.,

        # e.g.,
        # import FIFO::*;
        rule %r/(import\s+)(#{UPPER_IDENTIFIER}\s*)(::\s*\*+)/ do |m|  # Limited support for imports like FIFO#; TODO add support for RTL/IP imports
          token Keyword::Namespace, m[1]
          token Name::Namespace, m[2]
          token Punctuation, m[3]
        end

        rule(CONTROL, Keyword)  # TODO: could further split up semantically.
        rule(RESERVED, Keyword::Reserved)  # TODO: could further split up semantically.
        rule(SV_KEYWORDS, Keyword::Reserved)  # legacy words from SystemVerilog

        # Custom 
        rule(STANDALONE_CALL, Name::Attribute)
        rule(MATCH_UNPACK, Name::Variable)
        rule(METHOD_CALL, Name::Attribute)
        
        # To catch everything else
        rule(LOWER_IDENTIFIER, Name::Variable)
        rule(UPPER_IDENTIFIER, Name::Class)  # Lazy
        rule(WHITE_SPACE, Text::Whitespace)

        # For last because I don't want it overriding the special rules.
        rule(PUNCTUATION, Punctuation)
      end

      # e.g., Reg#(Bit#(2)) <- mkReg(0)
      #                        ^^^^^
      state :actionvalue do
        rule(/ #{LOWER_IDENTIFIER}/, Name::Attribute, :pop!)
        mixin :root
      end

      # e.g., module mkExample(Example);
      #              ^^^^^^^^^
      # e.g., method ActionValue#(Bit#(4)) do_thing(Bit#(4) input);
      #                                    ^^^^^^^^
      state :declared do
        rule(/ #{LOWER_IDENTIFIER}/, Name::Function, :pop!)
        mixin :root
      end

      # e.g., "Below is the format:\n%0x %b"
      #                            ^^*** **
      # where ^ is ESCAPED_CHAR and * is FORMAT_SPECIFIER
      state :string do
        rule(ESCAPED_CHAR, Str::Escape)
        rule(FORMAT_SPECIFIER, Str::Escape)
        rule(/"/, Str::Delimiter, :pop!)  # Needs to precede STRING_CHARACTER because it will capture everything else (by default)
        rule(/#{STRING_CHARACTER}/, Str)
      end

      state :namespace do
        rule(/ #{UPPER_IDENTIFIER}/, Name::Namespace)
        rule(/::/, Punctuation)  # technically redundant if we mixin root
        rule()
      end

      # Slightly overkill, but we can imagine a design pattern where we wish to be strict about what patterns may apply.
      # TODO add support for literal matches instead of just case matches
      state :case do
        rule(CASE_ENUM, Name::Constant)
        rule(/endcase/, Keyword::Reserved, :pop!)
        mixin :root
      end

      state :enum_declaration do
        rule(UPPER_IDENTIFIER, Name::Constant)
        rule(%r/}/, Punctuation, :pop!)
        mixin :root
      end
    end
  end
end
