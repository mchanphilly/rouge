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
      # Also TODO: conditional compilation (gray out `ifdef CONSTANT and `endif)

      # COMMENTS AND WHITESPACE
      # TODO: highlight TODO, NOTE, or other keywords of note inside of comments.
      LINE_COMMENT = /\/\/(?:(?!\n).)*/
      COMMENT = /#{LINE_COMMENT}/
      WHITE_SPACE = /\s+/

      # IDENTIFIERS
      IDENTIFIER_CHAR = /[A-Za-z0-9$_]/
      IDENTIFIER_TAIL = /#{IDENTIFIER_CHAR}*#?/

      # # is necessary for things like Bit#(5)
      UPPER_IDENTIFIER = /\b[[:upper:]]#{IDENTIFIER_TAIL}/  # (Identifier) package names, type names, enumeration labels, union members, and type classes
      # Leading _ is necessary for hidden instances; [DEC_DIGITS] is necessary for e.g. valids[5] <= True
      LOWER_IDENTIFIER = /\b[[:lower:]_]#{IDENTIFIER_TAIL}/  # (identifier) variables, modules, interfaces
      SYSTEM_IDENTIFIER = /\$#{IDENTIFIER_TAIL}/  # system tasks and functions
      HIDDEN_IDENTIFIER = /_#{IDENTIFIER_TAIL}/  # TODO unused

      def self.generic_declarations
        @generic_declarations ||= Set.new(%w(
          function instance interface method module package rule rules typeclass
          typedef struct tagged union enum endfunction endinstance endinterface
          endmethod endmodule endpackage endrule endrules endtypeclass
        ))
      end

      # TODO make this actually more regular instead of ad hoc
      # declared interface, module, function, method, rule names
      # I split the declarations into two types:
      #   1-degree named declarations (module/rule identifier)
      #   2-degree named declarations (second) (function/method RETURN_VALUE identifier)
      # both mixin the :root to cover up the rest of the rules
      # After writing out each of the rules, I realized you can combine the rules because
      # we can just pop after the first identifier.
      def self.special_declarations
        @special_declarations ||= Set.new(%w(
          module rule function method
        ))
      end
      # Pretty plausible that there are more declarations to add; but these cover a very solid portion of my usage.

      # KEYWORDS
      def self.control  # Mostly control; I slipped a type in there.
        @control ||= Set.new(%w(
          case endcase type else for if return while
        ))
      end
      
      def self.reserved
        @reserved ||= Set.new(%w(
          action endaction actionvalue endactionvalue ancestor clocked_by default
          default_clock default_reset dependencies e enable export ifc_inout import
          inout input_clock input_reset let match matches numeric output_clock
          output_reset parameter path port provisos deriving reset_by same_family
          schedule valueOf valueof void
        ))
      end

      def self.default_types  # Notice 
        @default_types ||= Set.new([
          "ActionValue#",  # The ordering is significant. We don't want to just capture the Action. (or we could use word boundaries)
          "Action",
          "bit",
          "let"
        ])
      end

      def self.special_keywords
        @special_keywords ||= Set.new(%w(
          BVI
          C
          CF
          E
          SB
          SBR
        ))
      end

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

      # TODO make these two rules ... not identical
      # TODO check if whitespace actually breaks method calls; if not, then we need to find a different rule. 
      METHOD_CALL = /\.#{LOWER_IDENTIFIER}/ # TODO make more robust; ideally it should follow a LOWER_IDENTIFIER
      # TODO see if we can color the . separately
      MATCH_UNPACK_VARIABLE = /\.#{LOWER_IDENTIFIER}/
      
      # An action function can stand alone.
      # We need to match the following:
      #   - do_thing;
      #   - do_thing(blah, blah, blah);
      # This regex checks that we have a newline, whitespace, and an identifier. We lookahead to check for ( or ;
      # STANDALONE_CALL = /(?m)^\n\s*#{LOWER_IDENTIFIER}(?=[\(;])/
      # CALL_NO_ARGUMENTS = /(#{STANDALONE_CALL}|#{METHOD_CALL})/
      # CALL_WITH_ARGUMENTS = /#{CALL_NO_ARGUMENTS}\w*(?=\()/
      # Compiler synthesis directives (TODO make not lazy)
      COMPILER_DIRECTIVE = /\(\*.*\*\)/

      # Operators
      PUNCTUATION = /(?:[.,;\(\)\{\}\[\]]|begin|end)/
      OPERATORS = /[\:=\+\-\!~&|\/%<>]+/  # TODO change to actual operators and not lazy

      # ENUM
      # Because enums and interfaces both use UPPER_IDENTIFIER, it can be difficult to distinguish
      # them in lexing. We need to be more discerning in the rules we use.
      
      # Looking at a snippet of Bluespec, we can see that generally (I don't know about strict
      # adherance to the grammar):
      #   Enumeration (members) are (and interfaces aren't):
      #   - in comma separated curly bracket lists {One, Two, Three} when defined
      #   - used with operators; e.g. comparison operator
      #   - in case statements

      CASE_ENUM = /#{UPPER_IDENTIFIER}(?=:)/

      # rule structure based on the go.rb lexer. It seemed very clean.

      # TODO combine similar rules that produce the same tokens
      state :simple_tokens do
        # Comment-like things
        mixin :whitespace

        # Keywords
        rule(SYSTEM_IDENTIFIER, Name::Builtin)  # e.g., $display, $format TODO check the word
        
        # Literals
        rule(REAL_LITERAL, Num)  # No more specific token available (has to be before)
        rule(INT_LITERAL, Num::Integer)
        # rule(ESCAPED_CHAR, Str::Escape)  # TODO (not implemented; need to play nicely with the string literal rule)
        rule(/"/, Str::Delimiter, :string)

        # Operators
        rule(/<-/, Operator, :actionvalue)
        rule(/<?=[^=]/, Operator, :assignment)  # Distinguish between = and ==

        rule(DONT_CARE, Keyword::Pseudo)
      end

      state :root do
        mixin :simple_tokens  # Mostly keywords

        # Special keyword cases (TODO merge with general case)
        rule(/\breturn\b/, Keyword, :assignment)  # Distinguish between = and ==
        rule(/\btypedef\b/, Keyword::Declaration, :typedef)
        rule %r/\binterface\b/ do
          token Keyword::Declaration
          push :interface unless state? :interface
        end
        rule(/\bcase\b/, Keyword::Reserved, :case)
        rule(/\bmatch\b/, Keyword::Reserved, :match_unpack)
        rule %r/(matches\s+)(tagged\s+)(#{UPPER_IDENTIFIER}\s+)(\.#{LOWER_IDENTIFIER})/ do |m|
          token Keyword::Reserved, m[1]
          token Keyword::Declaration, m[2]
          token Name::Class, m[3]
          token Name::Variable, m[4]
        end

        # e.g.,
        # import FIFO::*;
        rule %r/(import\s+)(#{UPPER_IDENTIFIER}\s*)(::\s*\*+)/ do |m|  # Limited support for imports like FIFO#; TODO add support for RTL/IP imports
          token Keyword::Namespace, m[1]
          token Name::Namespace, m[2]
          token Punctuation, m[3]
        end

        # TODO merge with general case
        # If we know a state-changing assignment is coming, then flag the left as an "action";
        # <= is a non-blocking assignment
        # This is a small abuse of the semantics, but I'm using the convention of Name::Attribute as a state-changing name.
        # supports both register_name <= new_value; and register_name[index] <= new_value
        ARRAY_INDEX = /\[\s*.+\s*\]/  # two brackets with anything in them.
        rule(/(#{LOWER_IDENTIFIER}\s*)(?=(#{ARRAY_INDEX}\s*)?<=)/, Name::Attribute)
        rule(/\[/, Punctuation, :index)

        # TODO merge with general case
        # Signal that there's a predicate ahead (either if or rule guard)
        # e.g.,  rule tick if (PREDICATE)
        # e.g.,  rule tick(PREDICATE)
        IFFOR_STATEMENT = /\b(?:(if|for))(\s*)(\()/
        RULE_DECLARATION = /(\brule\s+)(#{LOWER_IDENTIFIER}\s*)/
        RULE_PREDICATE_NOIF = /#{RULE_DECLARATION}(\()/
        
        rule IFFOR_STATEMENT do |m|
          token Keyword, m[1]
          token Text::Whitespace, m[2]
          token Punctuation, m[3]
          push :predicate
        end

        # TODO merge with declarations generally
        rule RULE_PREDICATE_NOIF do |m|
          token Keyword::Declaration, m[1]
          token Name::Function, m[2]
          token Punctuation, m[3]
          push :predicate
        end

        rule %r/#{LOWER_IDENTIFIER}(?=;)/ do
          if (in_state?(:assignment) or (in_state?(:index)) or (in_state?(:predicate)))
            token Name::Variable
          else 
            token Name::Attribute
          end
        end

        rule %r/#{LOWER_IDENTIFIER}(?=\()/ do
        if (in_state?(:assignment) or (in_state?(:index)) or (in_state?(:predicate)))
          token Name::Variable
          else 
            token Name::Attribute
          end
          push :argument_list  # Call with arguments
        end

        # Be aware that while some of these are bracket-like (interface/endinterface), they may also standalone (e.g. subinterface)
        # Process most other keywords and identifiers TODO absorb above "special" rules into below
        rule %r/(?:#{IDENTIFIER_CHAR}|#)+/ do |m|
          if self.class.default_types.include?(m[0])
            token Keyword
          elsif self.class.special_declarations.include?(m[0])
            # module, rule, interface, function, etc.
            token Keyword::Declaration
            push :declared
          elsif self.class.generic_declarations.include?(m[0])
            # endmodule, everything that's left, etc.,
            token Keyword::Declaration
          elsif self.class.special_keywords.include?(m[0])
            token Operator
          elsif self.class.control.include?(m[0])
            token Keyword
          elsif self.class.reserved.include?(m[0]) || self.class.sv_keywords.include?(m[0])
            # TODO: could further split up semantically.    # legacy words from SystemVerilog
            token Keyword::Reserved
          else  # Not in the above keywords? Must be custom.
            if m[0] =~ LOWER_IDENTIFIER
              token Name::Variable
            elsif m[0] =~ UPPER_IDENTIFIER
              token Name::Class
            else
              token Error
            end
          end
        end

        # For last because I don't want it overriding the special rules.
        rule(OPERATORS, Operator);  # TODO combine with above; leftover operators

        rule(PUNCTUATION, Punctuation)
      end

      # e.g., Reg#(Bit#(2)) <- mkReg(0)
      #                        ^^^^^
      state :actionvalue do
        rule(/\(/, Punctuation, :argument_list)
        # TODO fuse the two rules below
        rule(/#{LOWER_IDENTIFIER}\s*(?=\.)/, Name::Variable)  # Submodule about to have a method.
        rule(/#{LOWER_IDENTIFIER}\s*(?=[^\.])/, Name::Attribute)  # Function
        rule(/;/, Punctuation, :pop!) # exit on statement end ; 
        mixin :root
      end

      # e.g., module mkExample(Example);
      #              ^^^^^^^^^
      # e.g., method ActionValue#(Bit#(4)) do_thing(Bit#(4) input);
      #                                    ^^^^^^^^
      # but also be careful with red herrings, e.g.,
      #     method Bit#(TLog#(TAdd#(size, 1))) search1(Maybe#(t) r);
      #                             ^NO^       ^ YES ^   
      # TODO ideally this should all be refactored so we recognize the 
      # return value before looking for the identifier
      state :declared do  # It must either end (no args) or have a ( (yes args) or guard
        rule(/#{LOWER_IDENTIFIER}(?=\s*(?:[;\(]|if))/, Name::Function, :pop!)
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

      # e.g., import FIFO::*;
      #             ^^^^**
      state :namespace do
        rule(UPPER_IDENTIFIER, Name::Namespace)
        rule(/::/, Punctuation)  # technically redundant if we mixin root
      end

      # Slightly overkill, but we can imagine a design pattern where we wish to be strict about what patterns may apply.
      # TODO add support for literal matches instead of just case matches
      # e.g., case (condition)
      #            Example: do_something;
      #            AnotherExample: begin
      #                do_something_else;
      #            end
      #       endcase
      state :case do
        rule(CASE_ENUM, Name::Constant)
        # Note that tagged unpacking can come in two flavors: bracketed and unbracketed.
        #            tagged SubUnion1 {some_member: .sm, item: .i} :
        #            tagged SubUnion3 .v : $display(v); 
        rule(/\btagged\b/, Keyword::Declaration, :match_unpack)
        rule(/endcase/, Keyword, :pop!)
        mixin :root
      end

      state :typedef do
        rule(/;/, Punctuation, :pop!)  # TODO all these exits; make them zero width and only state change
        rule(/\benum\b/, Keyword::Declaration, :enum)
        rule(/\bstruct\b/, Keyword::Declaration, :struct)
        rule(/\bunion tagged\b/, Keyword::Declaration, :union)  # de facto word pair
        # Mostly just used for semantics
        mixin :root
      end

      state :enum do
        rule(/\{/, Punctuation, :enum_list)
        rule(UPPER_IDENTIFIER, Name::Class, :pop!)  # Likely name of enum
        mixin :root
      end

      state :struct do
        rule(/\{/, Punctuation, :struct_list)
        rule(UPPER_IDENTIFIER, Name::Class, :pop!)  # Likely the name of the struct
        mixin :root
      end
     
      state :union do
        rule(/\{/, Punctuation, :union_list)
        rule(UPPER_IDENTIFIER, Name::Class, :pop!)  # Name of the union
        mixin :root
      end

      # e.g.,
      # typedef enum {
      #     Good,
      #     Bad 
      # } Status deriving (Bits, Eq, FShow);
      state :enum_list do
        rule(UPPER_IDENTIFIER, Name::Constant)
        rule(/\}/, Punctuation, :pop!)
        mixin :root
      end

      # expect to see a list of statements with `TYPE name;``
      # We don't need to worry about semantics yet; just heuristic rules
      state :struct_list do
        rule(LOWER_IDENTIFIER, Name::Variable)
        rule(/\}/, Punctuation, :pop!)
        mixin :root
      end
      
      # Probably overkill number of states; 
      state :union_list do
        rule(/\benum\b/, Keyword::Declaration, :enum)
        rule(/\bstruct\b/, Keyword::Declaration, :struct)
        rule(/\bunion tagged\b/, Keyword::Declaration, :union)  # nested declaration
        rule(/\}/, Punctuation, :pop!)
        mixin :root
      end

      state :whitespace do
        rule(WHITE_SPACE, Text::Whitespace)
        rule(COMMENT, Comment)
        rule(/`ifdef.*?`endif/m, Comment)  # Assume not def
        rule(LAZY_DIRECTIVE, Comment::Preproc)  # `define, but with all `identifier
        rule(COMPILER_DIRECTIVE, Name::Function::Magic)  # e.g., (* synthesize *)
      end

      # TODO merge rules/states:
      #   1. raw_counter <- mkReg(Good);  [actionvalue]
      #   2. do_thing(Good);  [standalone call]
      #   3. submod.do_thing(Good);  [method call]
      # TODO test against nested parentheses
      state :argument_list do
        rule(LOWER_IDENTIFIER, Name::Variable)  # We suspect this is not an ActionValue function.
        rule(METHOD_CALL, Name::Variable)  # We suspect this is not an ActionValue method.
        rule(UPPER_IDENTIFIER, Name::Constant)
        rule(/\)/, Punctuation, :pop!)  # exit on close parenthesis
        mixin :root
      end

      # Corresponds to `tagged SubUnion .v :``
      state :match_unpack do
        rule(MATCH_UNPACK_VARIABLE, Name::Variable)
        rule(/\{/, Punctuation, :match_unpack_list)
        
        # : for tagged union matching;
        # = for struct matching 
        rule %r/[:=]/ do
          token Operator
          goto :assignment
        end
        mixin :root
      end

      # TODO Won't be robust with nested brackets.
      # Corresponds to bracketed match unpack `tagged SubUnion {some_member: .sm} :`
      state :match_unpack_list do
        rule(MATCH_UNPACK_VARIABLE, Name::Variable)
        rule(/\}/, Punctuation, :pop!)
        mixin :root
      end

      state :assignment do
        rule(/;/, Punctuation, :pop!)
        rule(/#{UPPER_IDENTIFIER}\s*(?=;)/, Name::Constant) # Very restricted enum instance assignnment
        mixin :root
      end

      state :predicate do
        rule(/\(/, Punctuation, :predicate)  # Nested predicate
        rule(/\)/, Punctuation, :pop!)  # Exit
        rule(/=/, Operator)  # Short-circuit; this is for for loops
        rule(UPPER_IDENTIFIER, Name::Constant)
        mixin :root
      end

      state :index do
        rule(/\]/, Punctuation, :pop!)
        mixin :root
      end

      state :interface do
        # Heuristically only interfaces and methods are members of interface.
        rule(/\bendinterface\b/, Keyword::Declaration, :pop!)  # top interface exit with endinterface
        rule(/#{LOWER_IDENTIFIER}\s*;/, Name::Function)
        # rule(/;/, Punctuation, :pop!)  # subinterface exit with ;
        mixin :root
      end
    end
  end
end
