const assert = require('node:assert/strict');
const { URI } = require('vscode-uri');
const { isHostFileUri, toServerUri, toEditorUri } = require('../../out/uris');

const script = URI.from({scheme:'vscode-remote', authority:'ssh-remote+devbox',
  path:'/home/ubuntu/project/sub/ExampleScript.sml'});
assert(isHostFileUri(script));
assert(isHostFileUri(URI.file('/tmp/ExampleScript.sml')));
assert(!isHostFileUri(URI.parse('git:/tmp/ExampleScript.sml')));
assert(!isHostFileUri(URI.parse('untitled:ExampleScript.sml')));
const server = toServerUri(script);
assert.equal(server, 'file:///home/ubuntu/project/sub/ExampleScript.sml');
assert.equal(toEditorUri(URI.parse(server), script).toString(), script.toString());
const dependency = URI.file('/home/ubuntu/.cache/holbuild/dep/AncestorScript.sml');
const editorDependency = toEditorUri(dependency, script);
assert.equal(editorDependency.scheme, 'vscode-remote');
assert.equal(editorDependency.authority, 'ssh-remote+devbox');
assert.equal(editorDependency.fsPath, dependency.fsPath);
assert.equal(toEditorUri(dependency, URI.file('/tmp/ExampleScript.sml')), dependency);
const unrelated = URI.parse('https://example.com/manual');
assert.equal(toEditorUri(unrelated, script), unrelated);
assert.equal(toServerUri(unrelated), unrelated.toString(true));
const revision = (file, ref, displayPath = file.fsPath) => file.with({
  scheme: 'git', path: displayPath,
  query: JSON.stringify({ path: file.fsPath, ref }),
});
const local = URI.file('/tmp/ExampleScript.sml');
const old = revision(local, 'HEAD~1', local.path + '.git');
const staged = revision(local, '');
assert.equal(toServerUri(old), local.toString(true));
assert.equal(toServerUri(staged), local.toString(true));
assert.equal(toEditorUri(local, old).toString(), old.toString());
assert.equal(toEditorUri(local, staged).toString(), staged.toString());
assert.equal(toEditorUri(dependency, old).toString(), dependency.toString());
const remoteRevision = revision(script, 'HEAD');
assert.equal(toServerUri(remoteRevision), server);
assert.equal(toEditorUri(URI.parse(server), remoteRevision).toString(),
  remoteRevision.toString());
assert.equal(toEditorUri(dependency, remoteRevision).toString(),
  editorDependency.toString());
const windowsRevision = URI.from({ scheme: 'git', path: '/c:/repo/ExampleScript.sml.git',
  query: JSON.stringify({ path: 'c:\\repo\\ExampleScript.sml', ref: 'HEAD' }) });
assert.equal(toServerUri(windowsRevision), 'file:///c:/repo/ExampleScript.sml');
console.log('Remote script synchronization and dependency navigation URI checks passed.');
