import type * as vscode from 'vscode';

/** Native paths are accessible on the workspace extension host. */
export function isHostFileUri(uri: Pick<vscode.Uri, 'scheme'>): boolean {
    return uri.scheme === 'file' || uri.scheme === 'vscode-remote';
}

/** Git's query names the real file, even when its display path ends in .git. */
export function sourceFileUri(uri: vscode.Uri): vscode.Uri {
    if (uri.scheme !== 'git') return uri;
    const filePath: string = JSON.parse(uri.query).path;
    const normalized = filePath.replace(/\\/g, '/');
    return uri.with({
        scheme: uri.authority ? 'vscode-remote' : 'file',
        path: normalized.startsWith('/') ? normalized : `/${normalized}`,
        query: '', fragment: '',
    });
}

/** HOL accepts filesystem URIs, not VS Code's Git or remote schemes. */
export function toServerUri(uri: vscode.Uri): string {
    uri = sourceFileUri(uri);
    return (uri.scheme === 'vscode-remote'
        ? uri.with({ scheme: 'file', authority: '' }) : uri).toString(true);
}

/** Server paths belong to the same host as the script, including caches. */
export function toEditorUri(uri: vscode.Uri, resource: vscode.Uri): vscode.Uri {
    if (resource.scheme === 'git' && uri.toString(true) === toServerUri(resource)) {
        return resource;
    }
    resource = sourceFileUri(resource);
    return uri.scheme === 'file' && resource.scheme === 'vscode-remote'
        ? uri.with({ scheme: resource.scheme, authority: resource.authority })
        : uri;
}
