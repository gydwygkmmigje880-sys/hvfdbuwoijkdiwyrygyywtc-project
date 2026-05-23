import { QuartzComponent, QuartzComponentConstructor, QuartzComponentProps } from "./types"
import { classNames } from "../util/lang"

const LectureMeta: QuartzComponent = ({ fileData, displayClass }: QuartzComponentProps) => {
  const fm = fileData.frontmatter ?? {}
  const speaker = fm["Докладчик"] as string | undefined
  const meeting = fm["Встреча"] as string | undefined
  const format = fm["Формат доклада"]
  const talkType = fm["Тип доклада"]

  const formatLabel = Array.isArray(format) ? format.join(", ") : format
  const typeLabel = Array.isArray(talkType) ? talkType.join(", ") : talkType

  if (!speaker && !meeting && !formatLabel && !typeLabel) {
    return null
  }

  return (
    <dl class={classNames(displayClass, "lecture-meta")}>
      {speaker && (
        <>
          <dt>Докладчик</dt>
          <dd>{speaker}</dd>
        </>
      )}
      {meeting && (
        <>
          <dt>Встреча</dt>
          <dd>{meeting}</dd>
        </>
      )}
      {formatLabel && (
        <>
          <dt>Формат</dt>
          <dd>{formatLabel}</dd>
        </>
      )}
      {typeLabel && (
        <>
          <dt>Тип</dt>
          <dd>{typeLabel}</dd>
        </>
      )}
    </dl>
  )
}

LectureMeta.css = `
.lecture-meta {
  display: grid;
  grid-template-columns: auto 1fr;
  gap: 0.25rem 1rem;
  margin: 0.5rem 0 1rem;
  padding: 0.75rem 1rem;
  border-radius: 8px;
  background: var(--highlight);
  color: var(--darkgray);
  font-size: 0.95rem;
}

.lecture-meta dt {
  margin: 0;
  font-weight: 600;
  color: var(--dark);
}

.lecture-meta dd {
  margin: 0;
}
`

export default (() => LectureMeta) satisfies QuartzComponentConstructor
