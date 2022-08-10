/*
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
*/
import * as React from "react"
import * as ReactDOM from "react-dom"
import * as penrose from "@penrose/core"
import * as SVG from "@svgdotjs/svg.js"

/** See [here](https://penrose.gitbook.io/penrose/#what-makes-up-a-penrose-program) for explanation. */
export interface PenroseTrio {
    dsl: string
    sty: string
    sub: string
}

async function hashTrio({dsl, sty, sub}: PenroseTrio): Promise<string> {
    // https://developer.mozilla.org/en-US/docs/Web/API/TextEncoder/encodeInto#buffer_sizing
    const data = new Uint8Array(3 * (dsl.length + sty.length + sub.length))
    const encoder = new TextEncoder()
    let dataView = data
    const {written} = encoder.encodeInto(dsl, dataView)
    dataView = data.subarray(written)
    const {written: written2} = encoder.encodeInto(sty, dataView)
    dataView = data.subarray(written2)
    encoder.encodeInto(sub, dataView)
    const digest = await crypto.subtle.digest("SHA-1", data)
    const digestArr = Array.from(new Uint8Array(digest))
    // https://developer.mozilla.org/en-US/docs/Web/API/SubtleCrypto/digest#converting_a_digest_to_a_hex_string
    return digestArr.map(b => b.toString(16).padStart(2, '0')).join('')
}

/** The compile -> optimize -> prepare SVG sequence is not cheap (on the order of 1s for a simple diagram),
 * so we aggressively cache its SVG outputs. */
// TODO(WN): provide a "redraw" button to resample a misshapen diagram.
const diagramSvgCache = new Map<string, SVGSVGElement>()

function aliasToNumber (x: SVG.NumberAlias): number {
    let y: string | number
    if (x instanceof Number) y = x.valueOf()
    else y = x as any

    if (typeof y === 'string') return parseFloat(y)
    else return y
}

async function renderPenroseTrio(trio: PenroseTrio, maxOptSteps: number): Promise<SVGSVGElement> {
    console.log(trio.sty)
    const hash = await hashTrio(trio)
    if (diagramSvgCache.has(hash)) return diagramSvgCache.get(hash)!
    const {dsl, sty, sub} = trio
    const compileRes = penrose.compileTrio({ domain: dsl, style: sty, substance: sub, variation: '' })
    if (compileRes.isErr()) throw new Error(penrose.showError(compileRes.error))
    const state = await penrose.prepareState(compileRes.value)
    const stateRes = penrose.stepUntilConvergence(state, maxOptSteps)
    if (stateRes.isErr()) throw new Error(penrose.showError(stateRes.error))
    if (!penrose.stateConverged(stateRes.value))
        console.warn(`Diagram failed to converge in ${maxOptSteps} steps`)
    const svg = await penrose.RenderStatic(stateRes.value, async path => path)

    // The canvas is usually too large, so trim the SVG as a postprocessing step
    const obj = SVG.SVG(svg)
    const view = obj.viewbox()
    let minX = view.width, maxX = 0, minY = view.height, maxY = 0

    obj.each((i, children) => {
        const child = children[i]
        minX = Math.min(minX, aliasToNumber(child.x()))
        maxX = Math.max(maxX, aliasToNumber(child.x()) + aliasToNumber(child.width()))
        minY = Math.min(minY, aliasToNumber(child.y()))
        maxY = Math.max(maxY, aliasToNumber(child.y()) + aliasToNumber(child.height()))
    })

    const padding = 10
    const newX = minX - padding, newY = minY - padding, newW = (maxX - minX) + padding, newH = (maxY - minY) + padding
    const newSvg = obj.viewbox(newX, newY, newW, newH).width(newW).height(newH)
    diagramSvgCache.set(hash, newSvg.node)

    return newSvg.node
}

export interface PenroseCanvasProps {
    trio: PenroseTrio
    maxOptSteps: number
    embedNodes: Map<string, React.ReactNode>
}

interface InnerWithContainerProps extends PenroseCanvasProps {
    containerDiv: HTMLDivElement
    hiddenDiv: HTMLDivElement
}

interface InnerWithEmbedsProps extends Omit<InnerWithContainerProps, 'embedNodes'> {
    embeds: Map<string, HTMLDivElement>
}

function InnerWithEmbeds({trio: {dsl, sty, sub}, maxOptSteps, embeds, containerDiv, hiddenDiv}: InnerWithEmbedsProps): JSX.Element {
    const containerRect = containerDiv.getBoundingClientRect()
    const dim = Math.ceil(Math.max(400, containerRect.width))

    sty = sty +
`
canvas {
    width = ${dim}
    height = ${dim}
}
`

    const cssColourToRgba = (col: string, alpha: number = 255) => {
        if (col.startsWith('#')) {
            const gps = col.match(/\w\w/g)
            if (!gps) throw new Error(`cannot parse colour '${col}'`)
            const [r, g, b] = gps.map(x => parseInt(x, 16))
            return `rgba(${r}/255,${g}/255,${b}/255,${alpha}/255)`
        } else throw new Error(`cannot parse colour '${col}'`)
    }

    const boxCol = cssColourToRgba(
        getComputedStyle(document.documentElement)
            .getPropertyValue('--vscode-editorHoverWidget-background'))

    for (const [name, elt] of embeds) {
        const rect = elt.getBoundingClientRect()

        // KC's hack: https://github.com/penrose/penrose/issues/1057#issuecomment-1164313880
        sty = sty +
`
forall Targettable \`${name}\` {
override \`${name}\`.textBox.width = ${Math.ceil(rect.width)}
override \`${name}\`.textBox.height = ${Math.ceil(rect.height)}
override \`${name}\`.textBox.fillColor = ${boxCol}
}
`
    }

    const [element, setElement] = React.useState<JSX.Element>(<pre>Drawing..</pre>)
    const [svg, setSvg] = React.useState<SVGSVGElement>()

    React.useEffect(() => {
        renderPenroseTrio({dsl, sty, sub}, maxOptSteps)
            .then(svg => {
                setElement(<>
                    <div ref={ref => {
                        if (!ref) return
                        if (ref.firstChild) ref.replaceChild(svg, ref.firstChild)
                        else ref.appendChild(svg)
                        setSvg(svg)
                    }} />
                </>)
            }).catch(ex => {
                setElement(<pre>Error while drawing: {ex.toString()}</pre>)
            })
    }, [dsl, sty, sub, maxOptSteps, embeds, containerDiv])

    // Position embeds over nodes in the SVG
    React.useEffect(() => {
        if (!svg) return

        // The boxes that we can draw interactive elements over
        const diagramBoxes = new Map<string, Element>()
        for (const gElt of svg.querySelectorAll("g, rect")) {
            if (!gElt.textContent) continue
            const gps = gElt.textContent.match(/`(\w+)`.textBox/)
            if (!gps) continue
            const name = gps[1]
            diagramBoxes.set(name, gElt)
        }

        for (const [name, gElt] of diagramBoxes) {
            const embedElt = embeds.get(name)
            if (!embedElt) continue
            const gRect = gElt.getBoundingClientRect()
            embedElt.style.top = `${gRect.top - containerRect.top}px`
            embedElt.style.left = `${gRect.left - containerRect.left}px`
        }

        hiddenDiv.style.visibility = 'visible'
    }, [svg])

    return element
}

function InnerWithContainer({trio, maxOptSteps, embedNodes, containerDiv, hiddenDiv}: InnerWithContainerProps): JSX.Element {
    const rect = containerDiv.getBoundingClientRect()
    const dim = Math.ceil(Math.max(400, rect.width))

    interface EmbedData {
        elt: HTMLDivElement | undefined
        portal: React.ReactPortal
    }

    const [embeds, setEmbeds] = React.useState<Map<string, EmbedData>>(new Map())
    // This is set once when all the embeds have been drawn
    const [embedsFinal, setEmbedsFinal] = React.useState<Map<string, HTMLDivElement>>()

    // Create portals for the embedded nodes; they will update `embeds` when rendered
    React.useEffect(() => {
        const newEmbeds: Map<string, EmbedData> = new Map()
        for (const [name, nd] of embedNodes) {
            const div = <div
                className="dib absolute"
                // Limit how wide nodes in the diagram can be
                style={{maxWidth: `${Math.ceil(dim / 5)}px`}}
                ref={newDiv => {
                    if (!newDiv) return
                    setEmbeds(embeds => {
                        const newEmbeds: Map<string, EmbedData> = new Map()
                        let changed = false
                        for (const [eName, data] of embeds) {
                            if (eName === name && data.elt !== newDiv) {
                                changed = true
                                newEmbeds.set(eName, {...data, elt: newDiv})
                            } else newEmbeds.set(eName, data)
                        }
                        return changed ? newEmbeds : embeds
                    })
            }}>{nd}</div>
            const portal = ReactDOM.createPortal(div, hiddenDiv, name)
            const data: EmbedData = {
                elt: undefined,
                portal
            }
            newEmbeds.set(name, data)
        }
        setEmbeds(newEmbeds)
    // `deps` must have constant size so we can't do a deeper comparison
    }, [embedNodes, hiddenDiv, dim])

    React.useEffect(() => {
        const embedDivs = new Map()
        for (const [name, {elt}] of embeds) {
            if (!elt) return
            embedDivs.set(name, elt)
        }
        if (embedDivs.size !== embedNodes.size) return
        setEmbedsFinal(embedDivs)
    }, [embeds, embedNodes])

    return <>
        {embedsFinal &&
            <InnerWithEmbeds trio={trio} maxOptSteps={maxOptSteps} embeds={embedsFinal}
                containerDiv={containerDiv} hiddenDiv={hiddenDiv} />}
        {Array.from(embeds.values()).map(({portal}) => portal)}
    </>
}

/** Renders an interactive [Penrose](https://github.com/penrose/penrose) diagram with the specified trio.
 * The Penrose optimizer is ran for at most `maxOptSteps`, a heuristic for when to stop trying.
 *
 * For every `[name, nd]` in `embedNodes` we locate an object with the same `name` in the substance
 * program, adjust the style program so that the object's dimensions match those of `nd`, and draw
 * the React node `nd` over `name` in the SVG diagram. */
export function PenroseCanvas(props: PenroseCanvasProps): JSX.Element {
    /* The implementation: do some work, store results, pass results as props to a nested component.
     * As opposed to doing everything in one component, nested components don't have to handle
     * partial results and are drawn atomically. The flow is:
     * - `PenroseCanvas` waits for the container div and an invisible `hiddenDiv`.
     * - `InnerWithContainer` uses `hiddenDiv` to render embedded nodes without displaying them,
     *   so that their sizes can be measured.
     * - `InnerWithEmbeds` adjusts the style program to match the sizes of embeds, draws the diagram,
     *   positions the embeds over it, and finally makes them visible. */

    const [containerDiv, setContainerDiv] = React.useState<HTMLDivElement | null>(null)
    const [hiddenDiv, setHiddenDiv] = React.useState<HTMLDivElement | null>(null)
    return <div className="relative" ref={setContainerDiv}>
        {containerDiv && hiddenDiv &&
            <InnerWithContainer {...props} containerDiv={containerDiv} hiddenDiv={hiddenDiv} />}
        <div style={{visibility: 'hidden'}} ref={setHiddenDiv} />
    </div>
}
