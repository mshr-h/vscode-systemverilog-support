// The module 'vscode' contains the VS Code extensibility API
// Import the necessary extensibility types to use in your code below
import {ExtensionContext, Position, TextDocument, CancellationToken, languages, Hover, HoverProvider} from 'vscode';

// This method is called when your extension is activated. Activation is
// controlled by the activation events defined in package.json.
export function activate(context: ExtensionContext) {
    // System Verilog Hover Provider
    context.subscriptions.push(
        languages.registerHoverProvider('systemverilog',
            new SystemVerilogHoverProvider()
        )
    );
}

class SystemVerilogHoverProvider implements HoverProvider {

    private _excludedText: RegExp;

    constructor() {
        this._excludedText = RegExp(/(reg|wire|input|output|logic|parameter|localparam|always|begin|end)/);
    }

    public provideHover(
        document: TextDocument, position: Position, token: CancellationToken):
        Hover {
            // text at current line
            let textLine = document.lineAt(position).text;

            // get word start and end
            let textRange = document.getWordRangeAtPosition(position);

            // hover word
            let targetText = textLine.substring(textRange.start.character, textRange.end.character);

            if (targetText.search(this._excludedText) !== -1) { // systemverilog keywords
                return;
            } else { // find declaration
                let declarationText = this._findDeclaration(document, position, targetText);
                if (declarationText !== undefined) {
                    let renderedText = '```systemverilog\n' + declarationText + '\n```';
                    return new Hover(renderedText);
                } else {
                    return;
                }
            }
    }

    private _findDeclaration(document: TextDocument, position: Position, target: string): string {
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
        for (let i = position.line-1; i >= 0; i--) {
            // text at current line
            let element = document.lineAt(i).text.replace(/\/\/.*/, '').trim().replace(/\s+/g, ' ');

            // find variable declaration type
            if (element.search(regexVariableTypeStart) !== -1) {
                // replace type to '', like input, output
                let subText = element.replace(regexVariableType, '').trim();

                // replace array to '', like [7:0]
                subText = subText.replace(/(\[.+?\])?/g, '').trim();
                if (subText.search(regexTarget) !== -1) {
                    return element;
                }
            }

            // find parameter declaration type
            if (element.search(regexParaType) !== -1) {
                return element;
            }
        }
    }
}
