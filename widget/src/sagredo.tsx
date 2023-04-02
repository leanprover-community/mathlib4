import { RpcContext, RpcPtr, mapRpcError } from '@leanprover/infoview'
import ReactMarkdown from 'react-markdown';
import * as React from 'react';

interface RpcData {
  k : RpcPtr<'Mathlib.Tactic.GPT.Sagredo.Widget.Data'>
}

type Msg = {
  kind: 'response'
  contents: string
  proof: string
} | {
  kind: 'query'
  contents: string
} | {
  kind: 'error'
  contents: string
}

interface NextQueryResponse {
  query: string
  data: any
}

interface RunQueryResponse {
  response: string
  proof: string
  data: any
}

function ChatBubble
    (props: React.DetailedHTMLProps<React.HTMLAttributes<HTMLDivElement>, HTMLDivElement>):
    JSX.Element {
  return (
    <div
        {...props}
        style={{
          ...props.style,
          backgroundColor: 'var(--vscode-editorHoverWidget-background)',
          borderColor: 'var(--vscode-editorHoverWidget-border)'
        }}
        className={'ba br3 pl3 pa2 shadow-1 mv2 ' + props.className}
      >
      {props.children}
    </div>
  )
}

export default function(data0: RpcData) {
  const rs = React.useContext(RpcContext)

  const [isAuto, setIsAuto] = React.useState<boolean>(false)

  type Status = 'waitingNextQuery' | 'preRunQuery' | 'waitingRunQuery' | 'done' | 'error'
  const [status, setStatus] = React.useState<Status>('waitingNextQuery')
  const [data, setData] = React.useState<RpcData>(data0)

  const [msgLog, setMsgLog] = React.useState<Msg[]>([])

  React.useEffect(() => {
    if (status === 'waitingNextQuery')
      rs.call<RpcData, NextQueryResponse>('nextQuery', data)
        .then(resp => {
          setMsgLog(ms => ms.concat([{ kind: 'query', contents: resp.query }]))
          setData(resp.data)
          // HACK: hardcoded output
          if (resp.query.includes('that proof works')) {
            setStatus('done')
          } else {
            setStatus('preRunQuery')
          }
        })
        .catch(e => {
          setMsgLog(ms => ms.concat([{ kind: 'error', contents: mapRpcError(e).message }]))
          setStatus('error')
        })
    if (status === 'preRunQuery' && isAuto)
      setStatus('waitingRunQuery')
    if (status === 'waitingRunQuery')
      rs.call<RpcData, RunQueryResponse>('runQuery', data)
        .then(resp => {
          setMsgLog(ms =>
              ms.concat([{ kind: 'response', contents: resp.response, proof: resp.proof}]))
          setData(resp.data)
          setStatus('waitingNextQuery')
        })
        .catch(e => {
          setMsgLog(ms => ms.concat([{ contents: mapRpcError(e).message, kind: 'error' }]))
          setStatus('error')
        })
  }, [status, isAuto])

  const stylesOfMsg = (msg: Msg) => {
    if (msg.kind === 'query')
      return 'w-80 self-end '
    if (msg.kind === 'response')
      return 'w-80 self-start '
    if (msg.kind === 'error')
      return 'bg-light-red '
  }

  return <details open>
    <summary className='mv2 pointer'>
      Sagredo
      <span className='fr'>
        <label>
          <input
            type='checkbox'
            className='mr1'
            checked={isAuto}
            onChange={() => setIsAuto(b => !b)} />
          Auto-send
        </label>
      </span>
    </summary>
    <div className='flex flex-column'>
      {msgLog.map((msg, iMsg) =>
        <ChatBubble className={stylesOfMsg(msg)}>
          {msg.kind === 'response' &&
            <div>
              Copy proof: {msg.proof}
            </div>}
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
          {iMsg === msgLog.length - 1 && status === 'preRunQuery' &&
            <button
                className='fr'
                onClick={() => setStatus('waitingRunQuery')}>
              Send
            </button>}
        </ChatBubble>)}
      {status === 'waitingNextQuery' && <ChatBubble>...</ChatBubble>}
      {status === 'waitingRunQuery' && <ChatBubble>Waiting for GPT..</ChatBubble>}
    </div>
  </details>
}
