module Rouge
  module Lexers
    class BluespecSystemVerilog < RegexLexer
      title "Bluespec SystemVerilog"
      desc "Bluespec SystemVerilog high-Level hardware description language"

      tag 'bluespec'
      aliases 'bsv'

      filenames '*.bsv', '*.ms'  # ms for Minispec
      
      # no BSV mimetype at time of writing

      def self.keywords
        @keywords ||= super + Set.new(%w(
          rule endrule
          method endmethod
          action endaction

          let
        ))
      end


      # All these rules translated from BNF in the BSV language reference guide

      # INTEGER LITERALS
      IDENTIFIER_TAIL = /[A-Za-z0-9$_]*\b/
      UPPER_IDENTIFIER = /\b[A-Z]#{IDENTIFIER_TAIL}/  # (Identifier) package names, type names, enumeration labels, union members, and type classes
      LOWER_IDENTIFIER = /\b[a-z]#{IDENTIFIER_TAIL}/  # (identifier) variables, modules, interfaces
      SYSTEM_IDENTIFIER = /\b[$]#{IDENTIFIER_TAIL}/  # system tasks and functions
      HIDDEN_IDENTIFIER = /\b[_]#{IDENTIFIER_TAIL}/  # 
      
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
      BASE_LITERAL = /(#{BASE_DEC_LITERAL}|#{BASE_HEX_LITERAL}|#{BASE_OCT_LITERAL}|#{BASE_BIN_LITERAL})/

      UNSIZED_INT_LITERAL = /#{SIGN}?(#{BASE_LITERAL}|#{DEC_NUM})/
      SIZED_INT_LITERAL = /#{BIT_WIDTH}#{BASE_LITERAL}/

      INT_LITERAL = /('0|'1|#{SIZED_INT_LITERAL}|#{UNSIZED_INT_LITERAL})/

      # REAL LITERALS

      # rule structure based on the go.rb lexer. It seemed very clean.
      state :simple_tokens do
        rule(INT_LITERAL, Num)
      end

      state :root do
        mixin :simple_tokens
      end

    end
  end
end
