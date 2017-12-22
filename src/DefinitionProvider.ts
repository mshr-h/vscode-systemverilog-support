import { Location, Position, TextDocument, CancellationToken, ProviderResult, Definition, DefinitionProvider } from 'vscode';

export class SystemVerilogDefinitionProvider implements DefinitionProvider {
  provideDefinition(document: TextDocument, position: Position, token: CancellationToken): ProviderResult<Definition> {
    // get word start and end
    let textRange = document.getWordRangeAtPosition(position);

    // hover word
    let targetText = document.getText(textRange);

    if (targetText.search(this._excludedText) !== -1) { // systemverilog keywords
      return;
    } else { // find declaration
      let result = this._findDeclaration(document, position, targetText);
      if (result !== undefined) {
        return new Location(document.uri, result);
      } else {
        return;
      }
    }
  }

  private _excludedText: RegExp;

  constructor() {
    this._excludedText = RegExp(/\b(alias|always|always_comb|always_ff|always_latch|and|assert|assign|assume|automatic|before|begin|bind|bins|binsof|bit|break|buf|bufif0|bufif1|byte|case|casex|casez|cell|chandle|class|clocking|cmos|config|const|constraint|context|continue|cover|covergroup|coverpoint|cross|deassign|default|defparam|design|disable|dist|do|edge|else|end|endcase|endclass|endclocking|endconfig|endfunction|endgenerate|endgroup|endinterface|endmodule|endpackage|endprimitive|endprogram|endproperty|endspecify|endsequence|endtable|endtask|enum|event|expect|export|extends|extern|final|first_match|for|force|foreach|forever|fork|forkjoin|function|generate|genvar|highz0|highz1|if|iff|ifnone|ignore_bins|illegal_bins|import|incdir|include|initial|inout|input|inside|instance|int|integer|interface|intersect|join|join_any|join_none|large|liblist|library|local|localparam|logic|longint|macromodule|matches|medium|modport|module|nand|negedge|new|nmos|nor|noshowcancelled|not|notif0|notif1|null|or|output|package|packed|parameter|pmos|posedge|primitive|priority|program|property|protected|pull0|pull1|pulldown|pullup|pulsestyle_onevent|pulsestyle_ondetect|pure|rand|randc|randcase|randsequence|rcmos|real|realtime|ref|reg|release|repeat|return|rnmos|rpmos|rtran|rtranif0|rtranif1|scalared|sequence|shortint|shortreal|showcancelled|signed|small|solve|specify|specparam|static|string|strong0|strong1|struct|super|supply0|supply1|table|tagged|task|this|throughout|time|timeprecision|timeunit|tran|tranif0|tranif1|tri|tri0|tri1|triand|trior|trireg|type|typedef|union|unique|unsigned|use|uwire|var|vectored|virtual|void|wait|wait_order|wand|weak0|weak1|while|wildcard|wire|with|within|wor|xnor|xor)\b/);
  }

  private _findDeclaration(document: TextDocument, position: Position, target: string): Position {
    // check target is valid variable name
    if (target.search(/[A-Za-z_][A-Za-z0-9_]*/g) === -1) {
      return;
    }

    let variableType = String.raw`\b(input|output|inout|reg|wire|logic|integer|bit|byte|shortint|int|longint|time|shortreal|real|double|realtime)\b\s+`;
    let variableTypeStart = '^' + variableType;
    let paraType = String.raw`^\b(parameter|localparam)\b\s+\b${target}\b`;

    let regexTarget = RegExp(String.raw`\b${target}\b`);
    let regexVariableType = RegExp(variableType, 'g');
    let regexVariableTypeStart = RegExp(variableTypeStart);
    let regexParaType = RegExp(paraType);

    // from previous line to first line
    for (let i = position.line - 1; i >= 0; i--) {
      // text at current line
      let line = document.lineAt(i).text;
      let element = line.replace(/\/\/.*/, '').trim().replace(/\s+/g, ' ');
      let lastChar = element.charAt(element.length - 1);
      if (lastChar === ',' || lastChar === ';') { // remove last ',' or ';'
        element = element.substring(0, element.length - 1);
      }

      // find variable declaration type
      if (element.search(regexVariableTypeStart) !== -1) {
        // replace type to '', like input, output
        let subText = element.replace(regexVariableType, '').trim();

        // replace array to '', like [7:0]
        subText = subText.replace(/(\[.+?\])?/g, '').trim();
        if (subText.search(regexTarget) !== -1) {
          return new Position(i, line.search(regexTarget));
        }
      }

      // find parameter declaration type
      if (element.search(regexParaType) !== -1) {
        return new Position(i, line.search(regexParaType));
      }
    }
  }
}