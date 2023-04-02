import { RpcContext, RpcPtr, mapRpcError } from '@leanprover/infoview'
import ReactMarkdown from 'react-markdown';
import * as React from 'react';

interface RpcData {
  k : RpcPtr<'Mathlib.Tactic.GPT.Sagredo.Widget.Data'>
}

type MsgKind = 'query' | 'response' | 'error'

interface Msg {
  contents : string
  kind : MsgKind
}

export default function(data: RpcData) {
  const [msgLog, setMsgLog] = React.useState<Msg[]>([])
  const rs = React.useContext(RpcContext)
  const renderQuery = (query: string) =>
    setMsgLog(ms => ms.concat([{ contents: query, kind: 'query' }]))
  const renderResponse = (response: string) =>
    setMsgLog(ms => ms.concat([{ contents: response, kind: 'response' }]))
  const callSagredo = (data: RpcData) =>
    rs.call<RpcData, [string, RpcData]>('nextQuery', data)
      .then(resp => {
        const [query, data] = resp
        renderQuery(query)
        rs.call<RpcData, [string, [string, RpcData]]>('runQuery', data)
          .then(resp => {
            const [text, [sol, data]] = resp
            renderResponse(text)
            callSagredo(data)
          })
        })
      .catch(e => setMsgLog(ms =>
        ms.concat([{ contents: mapRpcError(e).message, kind: 'error' }])))

  const stylesOfMsg = (msg: Msg) => {
    let ret = 'ba br3 pl3 pa2 shadow-1 mv2 '
    if (msg.kind === 'query')
      ret += 'w-80 self-end '
    if (msg.kind === 'response')
      ret += 'w-80 self-start '
    if (msg.kind === 'error')
      ret += 'bg-light-red '
    return ret
  }

  return <details open>
    <summary className='mv2 pointer'>Sagredo</summary>
    <button onClick={() => callSagredo(data)}>Go.</button>
    <div className='flex flex-column'>
      {msgLog.map(msg =>
        <div
            style={{
              backgroundColor: 'var(--vscode-editorHoverWidget-background)',
              borderColor: 'var(--vscode-editorHoverWidget-border)'
            }}
            className={stylesOfMsg(msg)}>
          <ReactMarkdown
            components={{
              pre: ({node, ...props}) => <pre {...props}
                className='pre-wrap br2 pa1 '
                style={{
                  backgroundColor: 'var(--vscode-textCodeBlock-background)',
                }} />,
              code: ({node, ...props}) =>
                props.inline ?
                  <code {...props}
                    className='font-code br2 '
                    style={{
                      backgroundColor: 'var(--vscode-textCodeBlock-background)',
                    }} /> :
                  <code {...props} className='font-code ' />
            }}
            children={msg.contents} />
        </div>)}
    </div>
  </details>
}
