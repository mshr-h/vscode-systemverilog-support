import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

export function instantiateModuleInteract() {
  let filePath = path.dirname(vscode.window.activeTextEditor.document.fileName);
  selectFile(filePath).then(srcpath => {
      let inst = instantiateModule(srcpath);
      vscode.window.activeTextEditor.insertSnippet(inst);
  });
}

function instantiateModule(srcpath: string) {
  if (!srcpath || !fs.statSync(srcpath).isFile) {
      return;
  }
  // remove comment
  let content = fs.readFileSync(srcpath, 'utf8').replace(/\/\/.*/g, '').replace(/\/\*[\s\S]*?\*\//g, '');
  if (content.indexOf('module') === -1) {
      return;
  }
  // module 2001 style
  let moduleIO = content.substring(content.indexOf('module'), content.indexOf(';'));
  let moduleName = moduleIO.match(/module\s+\b([A-Za-z_][A-Za-z0-9_]*)\b/)[1];
  let parametersName = [];
  let portsName = [];
  let data_inst = [];
  let lines = moduleIO.split('\n');

  // find all parameters and ports
  lines.forEach(line => {
      line = line.trim();
      let matched = line.match(/parameter\s+\b([A-Za-z_][A-Za-z0-9_]*)\b/);
      if (matched !== null) {
          parametersName.push(matched[1]);
      }

      if (line.search(/^\b(input|output|inout)\b/) !== -1) {
          let variables = line.replace(/\b(input|output|inout|reg|wire|logic|integer|bit|byte|shortint|int|longint|time|shortreal|real|double|realtime)\b/g, '')
              .replace(/(\[.+?\])?/g, '').replace(/\s+/g, '').split(',').forEach(variable => {
              if (variable) {
                  portsName.push(variable);
              }
          });
      }
  });

  if (portsName.length === 0) {
      return;
  }

  let prefix =
      vscode.workspace
      .getConfiguration("systemverilog")['instancePrefix'];

  let paramString = ``
  if (parametersName.length > 0) {
      paramString = `\n#(\n${instantiatePort(parametersName)})\n`
  }

  return new vscode.SnippetString()
      .appendText(moduleName + " ")
      .appendText(paramString)
      .appendPlaceholder(prefix)
      .appendPlaceholder(`${moduleName}(\n`)
      .appendText(instantiatePort(portsName))
      .appendText(');\n');
}

function instantiatePort(ports: string[]): string {
  let port = '';
  let max_len = 0;
  for (let i=0; i<ports.length; i++){
    if (ports[i].length > max_len)
      max_len = ports[i].length;
  }
  // .NAME(NAME)
  for (let i = 0; i < ports.length; i++) {
      let element = ports[i];
      let padding = max_len - element.length + 1;
      element = element + ' '.repeat(padding);
      port += `\t.${element}(${element})`;
      if (i !== ports.length - 1) {
          port += ',';
      }
      port += '\n';
  }
  return port;
}

function selectFile(currentDir?: string): Thenable<string> {
  currentDir = currentDir || vscode.workspace.rootPath;

  let dirs = getDirectories(currentDir);
  // if is subdirectory, add '../'
  if (currentDir !== vscode.workspace.rootPath) {
      dirs.unshift('..')
  }
  // all files ends with '.sv'
  let files = getFiles(currentDir)
      .filter(file => file.endsWith('.v') || file.endsWith('.sv'));

  // available quick pick items
  let items = dirs.concat(files);

  return vscode.window.showQuickPick(items)
      .then(selected => {
          if (!selected) {
              return;
          }

          // if is a directory
          let location = path.join(currentDir, selected);
          if (fs.statSync(location).isDirectory()) {
              return selectFile(location);
          }

          // return file path
          return location;
      });
}

function getDirectories (srcpath: string): string[] {
  return fs.readdirSync(srcpath)
      .filter(file => fs.statSync(path.join(srcpath, file)).isDirectory());
}

function getFiles (srcpath: string): string[] {
  return fs.readdirSync(srcpath)
      .filter(file => fs.statSync(path.join(srcpath, file)).isFile());
}