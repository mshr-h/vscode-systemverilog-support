// The module 'vscode' contains the VS Code extensibility API
// Import the necessary extensibility types to use in your code below
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import * as hover from './hover';
import * as inst from './instantiation'
import * as align from './alignment'

// This method is called when your extension is activated. Activation is
// controlled by the activation events defined in package.json.
export function activate(context: vscode.ExtensionContext) {
    // System Verilog Hover Provider
    let disposable = vscode.languages.registerHoverProvider('systemverilog', 
        new hover.SystemVerilogHoverProvider()
    );
    disposable = vscode.commands.registerCommand('extension.systemverilog.instantiateModule',
        inst.instantiateModuleInteract
    )
    disposable = vscode.commands.registerCommand('extension.systemverilog.alignment',
        align.alignment
    )
    context.subscriptions.push(disposable);

}
