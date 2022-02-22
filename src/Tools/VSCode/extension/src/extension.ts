'use strict';

import * as path from 'path'
import * as library from './library'
import * as decorations from './decorations'
import * as preview_panel from './preview_panel'
import * as protocol from './protocol'
import * as state_panel from './state_panel'
import { Uri, TextEditor, ViewColumn, Selection, Position, ExtensionContext, workspace, window,
  commands, ProgressLocation } from 'vscode'
import { LanguageClient, LanguageClientOptions, ServerOptions } from 'vscode-languageclient'
import { register_abbreviations } from './abbreviations'
import { Isabelle_FSP } from './isabelle_filesystem/isabelle_fsp'
import { Output_View_Provider } from './output_view'
import { register_script_decorations } from './script_decorations'


let last_caret_update: protocol.Caret_Update = {}

export async function activate(context: ExtensionContext)
{
  const isabelle_home = library.get_configuration<string>("home")
  const isabelle_args = library.get_configuration<Array<string>>("args")
  const cygwin_root = library.get_configuration<string>("cygwin_root")


  /* server */

  if (isabelle_home === "")
    window.showErrorMessage("Missing user settings: isabelle.home")
  else {
    const workspace_dir = await Isabelle_FSP.register(context)
    const roots = await workspace.findFiles("{ROOT,ROOTS}")
    const isabelle_tool = isabelle_home + "/bin/isabelle"
    const standard_args = ["-o", "vscode_unicode_symbols", "-o", "vscode_pide_extensions"]
    const session_args = roots.length > 0 ? ["-D", workspace_dir] : []

    const server_options: ServerOptions =
      library.platform_is_windows() ?
        { command:
            (cygwin_root === "" ? path.join(isabelle_home, "contrib", "cygwin") : cygwin_root) +
            "/bin/bash",
          args: ["-l", isabelle_tool, "vscode_server"].concat(standard_args, isabelle_args) } :
        { command: isabelle_tool,
          args: ["vscode_server"].concat(standard_args, isabelle_args, session_args) }

    const language_client_options: LanguageClientOptions = {
      documentSelector: [
        { language: "isabelle", scheme: Isabelle_FSP.scheme },
        { language: "isabelle-ml", scheme: "file" },
        { language: "bibtex", scheme: "file" }
      ],
      uriConverters: {
        code2Protocol: uri => Isabelle_FSP.get_file(uri).toString(),
        protocol2Code: value => Isabelle_FSP.get_isabelle(Uri.parse(value))
      }
    }

    const language_client =
      new LanguageClient("Isabelle", server_options, language_client_options, false)


    window.withProgress({location: ProgressLocation.Notification, cancellable: false},
      async (progress) =>
        {
          progress.report({
            message: "Waiting for Isabelle server..."
          })
          await language_client.onReady()
        })


    /* decorations */

    decorations.setup(context)
    context.subscriptions.push(
      workspace.onDidChangeConfiguration(() => decorations.setup(context)),
      workspace.onDidChangeTextDocument(event => decorations.touch_document(event.document)),
      window.onDidChangeActiveTextEditor(decorations.update_editor),
      workspace.onDidCloseTextDocument(decorations.close_document))

    language_client.onReady().then(() =>
      language_client.onNotification(protocol.decoration_type, decorations.apply_decoration))


    /* super-/subscript decorations */

    register_script_decorations(context)


    /* caret handling */

    function update_caret()
    {
      const editor = window.activeTextEditor
      let caret_update: protocol.Caret_Update = {}
      if (editor) {
        const uri = editor.document.uri
        const cursor = editor.selection.active
        if (library.is_file(uri) && cursor)
          caret_update = { uri: uri.toString(), line: cursor.line, character: cursor.character }
      }
      if (last_caret_update !== caret_update) {
        if (caret_update.uri) {
          caret_update.uri = Isabelle_FSP.get_file(Uri.parse(caret_update.uri)).toString()
          language_client.sendNotification(protocol.caret_update_type, caret_update)
        }
        last_caret_update = caret_update
      }
    }

    function goto_file(caret_update: protocol.Caret_Update)
    {
      function move_cursor(editor: TextEditor)
      {
        const pos = new Position(caret_update.line || 0, caret_update.character || 0)
        editor.selections = [new Selection(pos, pos)]
      }

      if (caret_update.uri) {
        caret_update.uri = Isabelle_FSP.get_isabelle(Uri.parse(caret_update.uri)).toString()
        workspace.openTextDocument(Uri.parse(caret_update.uri)).then(document =>
        {
          const editor = library.find_file_editor(document.uri)
          const column = editor ? editor.viewColumn : ViewColumn.One
          window.showTextDocument(document, column, !caret_update.focus).then(move_cursor)
        })
      }
    }

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        window.onDidChangeActiveTextEditor(_ => update_caret()),
        window.onDidChangeTextEditorSelection(_ => update_caret()))
      update_caret()

      language_client.onNotification(protocol.caret_update_type, goto_file)
    })


    /* dynamic output */

    const provider = new Output_View_Provider(context.extensionUri)
    context.subscriptions.push(
      window.registerWebviewViewProvider(Output_View_Provider.view_type, provider))

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.dynamic_output_type,
        params => provider.update_content(params.content))
    })


    /* state panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.state", uri => state_panel.init(uri)))

    language_client.onReady().then(() => state_panel.setup(context, language_client))


    /* preview panel */

    context.subscriptions.push(
      commands.registerCommand("isabelle.preview", uri => preview_panel.request(uri, false)),
      commands.registerCommand("isabelle.preview-split", uri => preview_panel.request(uri, true)))

    language_client.onReady().then(() => preview_panel.setup(context, language_client))


    /* Isabelle symbols and abbreviations */

    language_client.onReady().then(() =>
    {
      language_client.onNotification(protocol.session_theories_type,
        async ({entries}) => await Isabelle_FSP.init_workspace(entries))

      language_client.onNotification(protocol.symbols_type,
        params =>
          {
            //register_abbreviations(params.entries, context)
            Isabelle_FSP.update_symbol_encoder(params.entries)

            // request theories to load in isabelle file system
            // after a valid symbol encoder is loaded
            language_client.sendNotification(protocol.session_theories_request_type)
          })

      language_client.sendNotification(protocol.symbols_request_type)

    })


    /* spell checker */

    language_client.onReady().then(() =>
    {
      context.subscriptions.push(
        commands.registerCommand("isabelle.include-word", uri =>
          language_client.sendNotification(protocol.include_word_type)),
        commands.registerCommand("isabelle.include-word-permanently", uri =>
          language_client.sendNotification(protocol.include_word_permanently_type)),
        commands.registerCommand("isabelle.exclude-word", uri =>
          language_client.sendNotification(protocol.exclude_word_type)),
        commands.registerCommand("isabelle.exclude-word-permanently", uri =>
          language_client.sendNotification(protocol.exclude_word_permanently_type)),
        commands.registerCommand("isabelle.reset-words", uri =>
          language_client.sendNotification(protocol.reset_words_type)))
    })


    /* start server */

    context.subscriptions.push(language_client.start())
  }
}


export function deactivate() { }
