import { PageLayout, SharedLayout } from "./quartz/cfg"
import * as Component from "./quartz/components"
import { Options as ExplorerOptions } from "./quartz/components/Explorer"

const explorerSortFn: ExplorerOptions["sortFn"] = (a, b) => {
  const sectionOrder: Record<string, number> = {
    Доклады: 0,
    Статьи: 1,
    "Полезные материалы": 2,
  }

  if (a.isFolder && b.isFolder) {
    const orderA = sectionOrder[a.displayName] ?? 99
    const orderB = sectionOrder[b.displayName] ?? 99
    if (orderA !== orderB) return orderA - orderB
  }

  if ((!a.isFolder && !b.isFolder) || (a.isFolder && b.isFolder)) {
    return a.displayName.localeCompare(b.displayName, undefined, {
      numeric: true,
      sensitivity: "base",
    })
  }

  if (!a.isFolder && b.isFolder) {
    return 1
  }

  return -1
}

const explorerFilterFn: ExplorerOptions["filterFn"] = (node) => {
  if (node.slugSegment === "tags") return false
  // Hide only the homepage, keep folder index pages (e.g. Статьи/index)
  if (node.data?.slug === "index") return false
  return true
}

// components shared across all pages
export const sharedPageComponents: SharedLayout = {
  head: Component.Head(),
  header: [],
  afterBody: [],
  footer: Component.Footer({
    links: {
      GitHub: "https://github.com/jackyzha0/quartz",
      "Discord Community": "https://discord.gg/cRFFHYye7t",
    },
  }),
}

// components for pages that display a single page (e.g. a single note)
export const defaultContentPageLayout: PageLayout = {
  beforeBody: [
    Component.ConditionalRender({
      component: Component.Breadcrumbs(),
      condition: (page) => page.fileData.slug !== "index",
    }),
    Component.ConditionalRender({
      component: Component.ArticleTitle(),
      condition: (page) => page.fileData.slug !== "index",
    }),
    Component.ContentMeta(),
    Component.LectureMeta(),
    Component.TagList(),
  ],
  left: [
    Component.PageTitle(),
    Component.MobileOnly(Component.Spacer()),
    Component.Flex({
      components: [
        {
          Component: Component.Search(),
          grow: true,
        },
        { Component: Component.Darkmode() },
        { Component: Component.ReaderMode() },
      ],
    }),
    Component.Explorer({
      title: "",
      folderDefaultState: "open",
      folderClickBehavior: "link",
      useSavedState: false,
      sortFn: explorerSortFn,
      filterFn: explorerFilterFn,
    }),
  ],
  right: [
    Component.Graph(),
    Component.DesktopOnly(Component.TableOfContents()),
    Component.Backlinks(),
  ],
}

// components for pages that display lists of pages  (e.g. tags or folders)
export const defaultListPageLayout: PageLayout = {
  beforeBody: [Component.Breadcrumbs(), Component.ArticleTitle(), Component.ContentMeta()],
  left: [
    Component.PageTitle(),
    Component.MobileOnly(Component.Spacer()),
    Component.Flex({
      components: [
        {
          Component: Component.Search(),
          grow: true,
        },
        { Component: Component.Darkmode() },
      ],
    }),
    Component.Explorer({
      title: "",
      folderDefaultState: "open",
      folderClickBehavior: "link",
      useSavedState: false,
      sortFn: explorerSortFn,
      filterFn: explorerFilterFn,
    }),
  ],
  right: [],
}
